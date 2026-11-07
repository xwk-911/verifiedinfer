import Ptx.Kernels.AmpereTiledStage
import Ptx.Kernels.AmpereTiledAdvance
import Mathlib.Tactic.FinCases

/-! Exercise parameterized local rules with nonzero prior history and old C.
These arbitrary entry states are not claimed to be complete launch witnesses. -/
namespace Ptx.AmpereTiledStageTests
open Ptx.ISA Ptx.Ampere
noncomputable section

def ctx : Scalar.Context := {id := ⟨⟨2,1,0⟩,⟨3,7,0⟩⟩,block := ⟨4,8,1⟩}
def p : CopyStage.Pointers := ⟨64,320,1024,248,504,760⟩
def acc : Fin 4 → ℝ := fun i => if i.val = 0 then 2 else if i.val = 1 then 3 else if i.val = 2 then 5 else 7
def a : Fin 4 → PackedF16 := fun i => ⟨(2*i.val+1 : Nat),(2*i.val+2 : Nat)⟩
def b : Fin 2 → PackedF16 := fun i => ⟨(2*i.val+9 : Nat),(2*i.val+10 : Nat)⟩
def oracle : Oracle := {
  scalar := fun _ => .integer 0
  bytes := fun q => List.replicate 8 (.bits (byte q))
  word32 := fun q => if q = 14 then .packed (a 0) else if q = 15 then .packed (a 1)
    else if q = 16 then .packed (a 2) else if q = 17 then .packed (a 3)
    else if q = 18 then .packed (b 0) else .packed (b 1)
  matrix := fun q i => if q = 20 then 100+(i.val : ℝ) else -999
}
def payload (i : Fin 3) := oracle.bytes (11+i.val)
def prior : Copy := ⟨.ca,3,⟨.global,0⟩,⟨.shared ctx.id.cta,0⟩,List.replicate 8 (.bits (byte 7))⟩
def entry : State := {
  scalar := {
    core := {thread := {pc := 59,regs := [("%a",64),("%ah",320),("%b",1024),("%sa",248),("%sah",504),("%sb",760),
      ("%la",236),("%lb",748),("%tmp",999)]},queries := 11,generations := [(0,8)]}
    floats := [("%acc0",(.f32,2)),("%acc1",(.f32,3)),("%acc2",(.f32,5)),("%acc3",(.f32,7))]
  }
  copies := [prior]
  groups := 4
  mmaCalls := 2
}
def last := AmpereTiledStage.finalState ctx oracle entry p payload a b
def captured := AmpereTiledStage.call ctx oracle entry p payload a b acc

theorem parameterized_rule_instance : Ampere.run ctx oracle AmpereTiledStage.code 14 entry =
    .ok (last,AmpereTiledStage.events ctx oracle entry p payload 236 748 a b acc) := by
  apply AmpereTiledStage.execute ctx oracle entry p payload 236 748 a b acc rfl rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · rfl
  · rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i; simp [payload,oracle]
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl

theorem final_pc : last.scalar.core.thread.pc = 73 := by rfl
theorem final_queries : last.scalar.core.queries = 21 := by rfl
theorem final_groups : last.groups = 5 := by rfl
theorem final_copy_count : last.copies.length = 4 := by rfl
theorem final_mma_count : last.mmaCalls = 3 := by rfl
theorem final_generation : Ptx.Event.generation last.scalar.core 0 = 10 := by rfl
theorem old_c_captured : captured.inputs.c 0 = 2 := by rfl
theorem call_pc : captured.pc = 71 := by rfl
theorem call_ordinal : captured.ordinal = 2 := by rfl
theorem call_lane : captured.lane = 31 := by rfl
theorem output_reply_index : captured.output 0 = 100 := by simp [captured,AmpereTiledStage.call,AmpereTiledStage.answer,entry,payload,oracle,makeMmaCall]
theorem unrelated_register : lookup "%tmp" last.scalar.core.thread.regs = some 999 := by rfl

def nearWrap : State := {
  scalar := {core := {thread := {pc := 73,regs := [("%a",2^64-16),("%ah",2^64-32),("%b",2^64-1),("%it",2^32-16)]}}}
}
theorem wrapped_advance : Ampere.run ctx oracle AmpereTiledAdvance.code 5 nearWrap =
    .ok (AmpereTiledAdvance.nextState nearWrap (2^64-16) (2^64-32) (2^64-1) (2^32-16),[]) :=
  AmpereTiledAdvance.execute ctx oracle nearWrap _ _ _ _ rfl rfl rfl rfl rfl rfl

theorem wrapped_pointers :
    lookup "%a" (AmpereTiledAdvance.nextState nearWrap (2^64-16) (2^64-32) (2^64-1) (2^32-16)).scalar.core.thread.regs = some 16 ∧
    lookup "%ah" (AmpereTiledAdvance.nextState nearWrap (2^64-16) (2^64-32) (2^64-1) (2^32-16)).scalar.core.thread.regs = some 0 ∧
    lookup "%b" (AmpereTiledAdvance.nextState nearWrap (2^64-16) (2^64-32) (2^64-1) (2^32-16)).scalar.core.thread.regs = some 31 := by decide

end
end Ptx.AmpereTiledStageTests
