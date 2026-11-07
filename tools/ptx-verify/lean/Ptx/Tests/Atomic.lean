import Ptx.Kernels.AtomicDispatchTrace

/-! Exact source-interpreter runs and local typing/representation regressions.
These do not assert scoped global consistency or atomic-dispatch correctness. -/
namespace Ptx.AtomicTests
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

def ctx (id : ThreadId) : Scalar.Context := {
  id := id, params := [("Counter",0),("X",64),("Y",128)]
}
def oracle (value : Nat) : Scalar.Oracle := fun _ => .integer value
def baseRegs : Bindings := [("%rd2",128),("%rd1",64),("%rd0",0)]
def finalZero : Scalar.State := {
  core := {thread := {pc := 14,status := .done,regs := [("%r1",1),("%p0",1),("%r0",0)] ++ baseRegs},queries := 1}
}
def finalOne : Scalar.State := {
  core := {thread := {pc := 14,status := .done,regs := [("%r2",2),("%p1",1),("%p0",0),("%r0",1)] ++ baseRegs},queries := 1}
}
def finalOther (ticket : Nat) : Scalar.State := {
  core := {thread := {pc := 14,status := .done,regs := [("%p1",0),("%p0",0),("%r0",ticket)] ++ baseRegs},queries := 1}
}
def atomicEvent (value : Nat) : Scalar.Kind := .rmw .gpu ⟨.global,0⟩ (atomicAddBytes value 1)

theorem generated_types : Scalar.ProgramTyped Generated.atomic_dispatch.registerDeclarations
    Generated.atomic_dispatch.parameters code := Generated.atomic_dispatch.checked.valid

theorem source_ticket_zero (id : ThreadId) : Scalar.run (ctx id) (oracle 0) code 10 {} =
    .ok (finalZero,[atomicEvent 0,.write ⟨.global,64⟩ ((encodeU32 1).map Symbolic.Byte.bits)]) := by rfl

theorem source_ticket_one (id : ThreadId) : Scalar.run (ctx id) (oracle 1) code 11 {} =
    .ok (finalOne,[atomicEvent 1,.write ⟨.global,128⟩ ((encodeU32 2).map Symbolic.Byte.bits)]) := by rfl

/-- A locally legal reply can skip both jobs. Only the missing global scoped-RMW
memory argument can exclude this reply for a zero-initialized two-CTA launch. -/
theorem source_ticket_seventeen_locally_possible (id : ThreadId) : Scalar.run (ctx id) (oracle 17) code 10 {} =
    .ok (finalOther 17,[atomicEvent 17]) := by rfl

theorem source_unsigned_wrap (id : ThreadId) : Scalar.run (ctx id) (oracle 4294967295) code 10 {} =
    .ok (finalOther 4294967295,[atomicEvent 4294967295]) ∧
    (atomicAddBytes 4294967295 1).after = (encodeU32 0).map Symbolic.Byte.bits := by
  exact ⟨rfl,rfl⟩

/-- Raw oracle replies are normalized to the destination's u32 width. -/
theorem source_large_reply_wrap (id : ThreadId) : Scalar.run (ctx id) (oracle 4294967296) code 10 {} =
    .ok (finalZero,[atomicEvent 4294967296,.write ⟨.global,64⟩ ((encodeU32 1).map Symbolic.Byte.bits)]) := by rfl

def aliasState : Scalar.State := {core := {thread := {regs := [("%r",3)]}}}
def aliasCode : List Scalar.Instr := [.atomAddU32 "%r" {base := .imm 64} (.reg "%r")]
theorem increment_reads_before_destination_write (id : ThreadId) :
    Scalar.step (ctx id) (oracle 7) aliasCode aliasState = .ok
      (finishInteger aliasState {aliasState.core with thread := assign aliasState.core.thread "%r" 7,queries := 1},
        [.rmw .gpu ⟨.global,64⟩ (atomicAddBytes 7 3)]) := by rfl

theorem real_reply_rejected (id : ThreadId) (value : ℝ) :
    Scalar.step (ctx id) (fun _ => .real .f32 value) aliasCode aliasState = .error (.oracleType 0) := by rfl

theorem float_destination_rejected : ¬ Scalar.InstructionTyped [("%f",.floating .f32)] [] 1
    (.atomAddU32 "%f" {base := .imm 64} (.imm 1)) := by decide

theorem narrow_pointer_rejected : ¬ Scalar.InstructionTyped [("%r",.integer .u32)] [] 1
    (.atomAddU32 "%r" {base := .reg "%r"} (.imm 1)) := by decide

theorem both_byte_projections : (atomicEvent 7).readByte ⟨.global,0⟩ = some (.bits (byte 7)) ∧
    (atomicEvent 7).writeByte ⟨.global,0⟩ = some (.bits (byte 8)) ∧
    (atomicEvent 7).footprint = some (⟨.global,0⟩,4) := by exact ⟨rfl,rfl,rfl⟩

theorem mixed_width_rmw_payload_impossible :
    ¬ ∃ bytes : Event.RmwBytes Byte, bytes.before = encodeU32 0 ∧ bytes.after = [byte 1] := by
  rintro ⟨bytes,hbefore,hafter⟩
  have h := bytes.sameSize
  simp [hbefore,hafter] at h

theorem cta_scope_excludes_peer : ¬ Scope.cta.Includes ⟨⟨0,0,0⟩,.zero⟩ ⟨⟨1,0,0⟩,.zero⟩ := by decide
theorem gpu_scope_includes_peer (a b : ThreadId) : Scope.gpu.Includes a b := True.intro

end
end Ptx.AtomicTests
