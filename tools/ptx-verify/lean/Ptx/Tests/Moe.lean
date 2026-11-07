import Ptx.Kernels.MoeRouteThread
import Ptx.Generated.MoeExperts
import Ptx.Generated.MoeCombine

/-! MoE stage data, independent math and actual local routing regressions.
These are NOT global consistency/composition witnesses for the three stages. -/
namespace Ptx.MoeTests
open Ptx.ISA Ptx.Scalar
noncomputable section

theorem route_typed : Scalar.ProgramTyped Generated.moe_route.registerDeclarations
    Generated.moe_route.parameters Generated.moe_route.program := Generated.moe_route.checked.valid
theorem experts_typed : Scalar.ProgramTyped Generated.moe_experts.registerDeclarations
    Generated.moe_experts.parameters Generated.moe_experts.program := Generated.moe_experts.checked.valid
theorem combine_typed : Scalar.ProgramTyped Generated.moe_combine.registerDeclarations
    Generated.moe_combine.parameters Generated.moe_combine.program := Generated.moe_combine.checked.valid

def gates (a b : ℝ) : Moe.Matrix := fun _ col => if col = 0 then a else b
def ready (a b : ℝ) (dst : Nat) : Scalar.State := {
  core := {thread := {pc := 16,regs := [("%rp",dst),("%keep",33)]},queries := 7}
  floats := [("%g1",(.f32,b)),("%g0",(.f32,a))]
}
theorem suffix_ready (a b : ℝ) (dst : Nat) : MoeRouteSelect.Ready (gates a b) 0 dst (ready a b dst) := by
  constructor <;> simp [ready,gates,lookup,declarationLookup]

theorem route_left (a b : ℝ) (h : b ≤ a) : Moe.selected (gates a b) 0 = 0 := by
  apply Moe.selected_zero
  simpa [gates] using h
theorem route_right (a b : ℝ) (h : a < b) : Moe.selected (gates a b) 0 = 1 := by
  apply Moe.selected_one
  simpa [gates] using h
theorem route_tie (a : ℝ) : Moe.selected (gates a a) 0 = 0 := route_left a a (le_refl a)

theorem actual_right_suffix (ctx : Scalar.Context) (oracle : Scalar.Oracle) :
    Scalar.run ctx oracle Generated.moe_route.program 6 (ready (-3) (-2) 72) =
      .ok (MoeRouteSelect.final (ready (-3) (-2) 72) 1,[.write ⟨.global,72⟩ (u32Bytes 1)]) := by
  have h := MoeRouteSelect.complete_suffix ctx oracle (gates (-3) (-2)) 0 72
    (suffix_ready _ _ _) (by norm_num)
  simpa [MoeRouteSelect.code,route_right (-3) (-2) (by norm_num)] using h
theorem actual_tie_suffix (ctx : Scalar.Context) (oracle : Scalar.Oracle) (a : ℝ) :
    Scalar.run ctx oracle Generated.moe_route.program 6 (ready a a 72) =
      .ok (MoeRouteSelect.final (ready a a 72) 0,[.write ⟨.global,72⟩ (u32Bytes 0)]) := by
  have h := MoeRouteSelect.complete_suffix ctx oracle (gates a a) 0 72 (suffix_ready _ _ _) (by norm_num)
  simpa [MoeRouteSelect.code,route_tie] using h
theorem suffix_queries_preserved (a b : ℝ) (e : Nat) :
    (MoeRouteSelect.final (ready a b 72) e).core.queries = 7 := MoeRouteSelect.final_queries _ _

theorem predicate_bank_and_frame (a b : ℝ) :
    lookup "%p" (intAssign (ready a b 72) "%p" (gtFlag b a)).core.thread.regs = some (gtFlag b a) ∧
    declarationLookup "%p" (intAssign (ready a b 72) "%p" (gtFlag b a)).floats = none ∧
    lookup "%keep" (intAssign (ready a b 72) "%p" (gtFlag b a)).core.thread.regs = some 33 := by
  simp [ready,lookup]

def x : Moe.Matrix := fun row item => (2*row+item+1 : Nat)
def weights : Moe.Weights := fun e item col => (6*e+3*item+col+1 : Nat)
theorem first_expert_output : Moe.output (gates 4 1) x weights 0 0 2 = 9 := by
  norm_num [Moe.output,Moe.linear,Moe.selected,gates,x,weights]
theorem second_expert_output : Moe.output (gates (-2) 3) x weights 1 2 2 = 75 := by
  norm_num [Moe.output,Moe.linear,Moe.selected,gates,x,weights]
theorem tied_expert_output : Moe.output (gates 7 7) x weights 2 0 2 = 29 := by
  norm_num [Moe.output,Moe.linear,Moe.selected,gates,x,weights]

theorem comparison_bad_types :
    ¬ Scalar.InstructionTyped [("%r",.integer .u32),("%f",.floating .f32)] [] 1
      (.setpGt .f32 "%r" (.reg "%f") (.reg "%f")) ∧
    ¬ Scalar.InstructionTyped [("%p",.integer .pred),("%r",.integer .u32),("%f",.floating .f32)] [] 1
      (.setpGt .f32 "%p" (.reg "%r") (.reg "%f")) := by decide

def input : MoeRouteThread.Inputs := ⟨64,128,3,by norm_num,by norm_num,by norm_num⟩
def context : Scalar.Context := {
  id := {cta := ⟨1,0,0⟩,tid := .zero}
  block := ⟨2,1,1⟩
  params := [("G",64),("R",128),("M",3)]
}
theorem params : MoeRouteThread.Params input context.params := by
  constructor <;> norm_num [input,context,lookup]
theorem bounds : MoeRouteThread.Bounds context := by
  constructor <;> norm_num [context,col,Dim3.zero]
theorem actual_entry_tie_witness : ∃ final,
    Scalar.run context (fun _ => .real .f32 7) Generated.moe_route.program 22 {} =
      .ok (final,[.read ⟨.global,80⟩ (Symbolic.encode .f32 7),
                  .read ⟨.global,84⟩ (Symbolic.encode .f32 7),
                  .write ⟨.global,136⟩ (u32Bytes 0)]) ∧ final.core.thread.status = .done := by
  have h := MoeRouteThread.active_run input context (fun _ => .real .f32 7) (gates 7 7)
    params bounds (by norm_num [input,context,col,Dim3.zero]) (by norm_num [input,context,col,Dim3.zero])
    (by norm_num [input,context,col,Dim3.zero]) (by simp [gates]) (by simp [gates])
  refine ⟨MoeRouteSelect.final (MoeRouteThread.loaded input context 7 7) 0,?_,rfl⟩
  simpa [MoeRouteThread.code,MoeRouteThread.reads,input,context,col,Dim3.zero,gates,Moe.selected] using h

theorem actual_empty_no_reads (oracle : Scalar.Oracle) :
    Scalar.run {context with params := [("G",0),("R",0),("M",0)]} oracle
      Generated.moe_route.program 11 {} = .ok
      (MoeRouteThread.maskedFinal ⟨0,0,0,by norm_num,by norm_num,by norm_num⟩
        {context with params := [("G",0),("R",0),("M",0)]},[]) := by
  apply MoeRouteThread.masked_run
  · constructor <;> simp [lookup]
  · constructor <;> norm_num [context,col,Dim3.zero]
  · norm_num [context,col,Dim3.zero]

end
end Ptx.MoeTests
