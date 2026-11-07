import Ptx.Scalar.Rules
import Ptx.Kernels.CopyEvent
import Mathlib.Tactic.NormNum

/-! Symbolic-float local execution evidence, not a completed weak-memory kernel
contract or GPU test. Mechanically translated float fixtures and their separate
local provenance tests are in Tests/FloatFrontend.lean.
-/
namespace Ptx.ScalarTests
open Ptx.ISA Ptx.Scalar
noncomputable section

def ctx : Event.Context := ⟨⟨.zero,.zero⟩,[]⟩
def program : Scalar.CheckedProgram := {
  registers := [("%a",.floating .f32),("%b",.floating .f32),("%c",.floating .f32),("%out",.floating .f32)]
  parameters := []
  code := [.load .f32 .global "%a" {base := .imm 0},.load .f32 .global "%b" {base := .imm 4},
    .load .f32 .global "%c" {base := .imm 8},.fmaRn .f32 "%out" (.reg "%a") (.reg "%b") (.reg "%c"),
    .store .f32 .global {base := .imm 12} (.reg "%out"),.integer .ret]
  valid := by decide
}

def oracle (a b c : ℝ) : Scalar.Oracle := fun query => .real .f32 (if query = 0 then a else if query = 1 then b else c)
def finalState (a b c : ℝ) : Scalar.State := {
  core := {thread := {pc := 5,status := .done},queries := 3}
  floats := [("%out",(.f32,a*b+c)),("%c",(.f32,c)),("%b",(.f32,b)),("%a",(.f32,a))]
}
def beforeRet (a b c : ℝ) : Scalar.State := {
  core := {thread := {pc := 5},queries := 3}
  floats := (finalState a b c).floats
}
def events (a b c : ℝ) : List Scalar.Kind := [
  .read ⟨.global,0⟩ (Symbolic.encode .f32 a),.read ⟨.global,4⟩ (Symbolic.encode .f32 b),
  .read ⟨.global,8⟩ (Symbolic.encode .f32 c),.write ⟨.global,12⟩ (Symbolic.encode .f32 (a*b+c))]

theorem load_fma_store_trace (a b c : ℝ) : Scalar.run ctx (oracle a b c) program.code 6 {} =
    .ok (finalState a b c,events a b c) := by
  have hp : Scalar.run ctx (oracle a b c) program.code 5 {} = .ok (beforeRet a b c,events a b c) := by
    simp [Scalar.run,Scalar.step,program,oracle,Scalar.eval,writeFloat,
      Scalar.require,liftInteger,evalAddr,Ptx.eval,wrap,advance,
      declarationLookup,Location.resolve,beforeRet,finalState,events,
      bind,Except.bind,pure,Except.pure]
  have ht : Scalar.step ctx (oracle a b c) program.code (beforeRet a b c) = .ok (finalState a b c,[]) := by
    have h := Scalar.integer_local_step (ctx := ctx) (oracle := oracle a b c) (code := program.code)
      (s := beforeRet a b c) rfl rfl rfl (by intro bid h; cases h) rfl
    simpa [finishInteger,beforeRet,finalState,lookup] using h
  rw [show 6 = 5+1 by decide,Scalar.run_add,hp]
  simp [Scalar.run,ht,Except.bind]

theorem source_literals :
    (F32Literal.mk 0 (by decide) (by decide)).value = 0 ∧
    (F32Literal.mk 1065353216 (by decide) (by decide)).value = 1 ∧
    (F32Literal.mk 2147483648 (by decide) (by decide)).value = 0 := by
  norm_num [F32Literal.value]

theorem fragmented_width_rejected (value : ℝ) :
    Symbolic.decode .f32 (Symbolic.encode .f16 value) = none :=
  Symbolic.decode_length_mismatch (by simp [Symbolic.Format.bytes])

def overwrittenCode : List Scalar.Instr := [.integer .ret,.integer (.mov 32 "%x" (.imm 7)),
  .addRn .f32 "%y" (.reg "%x") (.reg "%x")]
def integerAfter : Event.State := {thread := {pc := 2,regs := [("%x",7)]}}

theorem integer_overwrite_clears_float (value : ℝ) :
    Scalar.step ctx (fun _ => .integer 0) overwrittenCode (writeFloat {} "%x" .f32 value) =
      .ok (⟨integerAfter,[]⟩,[]) := by
  have hs : localStep ctx.params ctx.id.tid.x (writeFloat {} "%x" .f32 value).core.thread
      (.mov 32 "%x" (.imm 7)) = .ok integerAfter.thread := by
    simp [localStep,writeFloat,integerAfter,advance,assign,put,wrap,Ptx.eval,bind,Except.bind,pure,Except.pure]
  have h := Scalar.integer_local_step (ctx := ctx) (oracle := fun _ => .integer 0) (code := overwrittenCode)
    (s := writeFloat {} "%x" .f32 value) rfl rfl rfl (by intro bid h; cases h) hs
  simpa [finishInteger,writeFloat,integerAfter,lookup] using h

theorem stale_float_read_rejected : Scalar.step ctx (fun _ => .integer 0) overwrittenCode ⟨integerAfter,[]⟩ =
    .error (.floatRegister "%x") := by
  simp [Scalar.step,integerAfter,overwrittenCode,Scalar.require,Scalar.eval,declarationLookup,
    bind,Except.bind]

theorem float_write_clears_integer (value : ℝ) :
    let start : Scalar.State := {core := {thread := {regs := [("%x",999)]}}}
    lookup "%x" (writeFloat start "%x" .f32 value).core.thread.regs = none ∧
      Scalar.eval .f32 (writeFloat start "%x" .f32 value) (.reg "%x") = .ok value :=
  ⟨float_write_invalidates_integer _ _ _ _,eval_written_float _ _ _ _⟩

theorem native_float_as_integer_rejected :
    ¬ Scalar.InstructionTyped [("%f",.floating .f32)] [] 1 (.integer (.mov 32 "%f" (.imm 0))) ∧
    ¬ Scalar.InstructionTyped [("%x",.integer .u32)] [] 1 (.mov .f32 "%x" (.reg "%x")) := by decide

/-- The same universal Copy trace still executes under the scalar extension.
This is a conservative-extension theorem, not a selected finite sample. -/
theorem original_copy_trace (c : CopyContract.Config) (tid : Nat) (oldOracle : Event.Oracle) (params : Bindings)
    (ht : tid < c.count) (hp : CopyContract.Params c params) (ha : tid < c.n) :
    Scalar.run (CopyEvent.context tid params) (embedOracle oldOracle) (CopyEvent.code.map Scalar.Instr.integer) 12 {} =
      .ok (embedState (CopyEvent.activeFinal c tid (oldOracle 0)),
        (CopyEvent.events c tid (oldOracle 0)).map liftKind) := by
  change Scalar.run _ _ _ 12 (embedState {}) = _
  rw [run_integer,CopyEvent.run_active c tid oldOracle params ht hp ha]
  rfl

end
end Ptx.ScalarTests
