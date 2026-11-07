import Ptx.Kernels.ScalarAttentionOuter

/-! Concrete full-source nonempty attention execution, including BOTH softmax
branches and a changed maximum. This remains local source execution evidence;
global consistency/observation and the all-candidate contract are separate. -/
namespace Ptx.ScalarAttentionOuterTests
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttentionOuter
noncomputable section

def layout : Layout := {
  keys := 2, dim := 1, qBase := 0, keyBase := 64, valueBase := 128, output := 256, firstQuery := 1
  keys32 := by decide
  dim32 := by decide
  output64 := by decide
  qRead64 := by
    intro k hk
    have he : k = 0 := by omega
    subst k
    norm_num
  keyRead64 := by
    intro j k hj hk
    have he : k = 0 := by omega
    subst k
    omega
  valueRead64 := by intro j hj; omega
}
def ctx : Scalar.Context := {
  id := ⟨.zero,.zero⟩
  params := [("Q",0),("K",64),("V",128),("O",256),("Scale",320),("M",1),("N",2),("D",1)]
}
def q : Attention.Matrix := fun _ _ => 1
def key : Attention.Matrix := fun item _ => if item = 0 then 0 else 1
def value : Attention.Matrix := fun item _ => if item = 0 then 4 else 10
def oracle : Scalar.Oracle := fun query => .real .f32
  (if query = 0 then 1 else if query = 1 then 1 else if query = 2 then 0 else
   if query = 3 then 4 else if query = 4 then 1 else if query = 5 then 1 else 10)
def literalZero : ℝ := (F32Literal.mk 0 (by decide) (by decide)).value
def ready : Scalar.State := {
  core := {queries := 1,thread := {pc := 37,regs := [
    ("%j",0),("%stride",4),("%vp",128),("%qr",0),("%p",0),("%op",256),("%offset",0),
    ("%col",0),("%tx",0),("%sx",1),("%bx",0),("%row",0),("%ty",0),("%sy",1),("%by",0),
    ("%d",1),("%n",2),("%m",1),("%sp",320),("%o",256),("%kr",64),("%q",0)]}}
  floats := [("%scale",(.f32,1)),("%out",(.f32,literalZero))]
}

theorem prefix_source : Scalar.run ctx oracle code 37 {} =
    .ok (ready,[.read ⟨.global,320⟩ (Symbolic.encode .f32 1)]) := rfl

theorem ready_banks : BanksDisjoint ready := by
  intro name
  by_cases hs : name = "%scale"
  · subst name; left; rfl
  by_cases ho : name = "%out"
  · subst name; left; rfl
  · right; simp [ready,declarationLookup,Ne.symm hs,Ne.symm ho]

theorem ready_online_uninitialized : declarationLookup "%max" ready.floats = none ∧
    declarationLookup "%l" ready.floats = none ∧ declarationLookup "%u" ready.floats = none := by
  exact ⟨rfl,rfl,rfl⟩

theorem source_counts : iterationSteps layout.dim 0 = 28 ∧ iterationSteps layout.dim 1 = 35 ∧
    suffixSteps layout.dim 0 layout.keys = 68 ∧ queryIndex layout 0 = 1 ∧ queryIndex layout 1 = 4 := by decide

theorem ready_inv : Inv layout (scores layout q key 1 0) (fun item => value item 0) 1 0 ready := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro h; exact (h rfl).elim
  · exact ready_banks

theorem q_replies : ∀ j k, j < layout.keys → k < layout.dim →
    oracle (queryIndex layout j+2*k) = .real .f32 (q 0 k) := by
  intro j k hj hk
  have he : k = 0 := by change k < 1 at hk; omega
  subst k
  have he : j = 0 ∨ j = 1 := by change j < 2 at hj; omega
  rcases he with rfl | rfl <;> rfl

theorem key_replies : ∀ j k, j < layout.keys → k < layout.dim →
    oracle (queryIndex layout j+2*k+1) = .real .f32 (key j k) := by
  intro j k hj hk
  have he : k = 0 := by change k < 1 at hk; omega
  subst k
  have he : j = 0 ∨ j = 1 := by change j < 2 at hj; omega
  rcases he with rfl | rfl <;> rfl

theorem value_replies : ∀ j, j < layout.keys → oracle (queryIndex layout j+2*layout.dim) = .real .f32 (value j 0) := by
  intro j hj
  have he : j = 0 ∨ j = 1 := by change j < 2 at hj; omega
  rcases he with rfl | rfl <;> rfl

theorem independent_output : Attention.output q key value (Real.log 2*1) 0 0 layout.keys layout.dim = 8 := by
  norm_num [Attention.output,Attention.numerator,Attention.denominator,Attention.score,Attention.dot,
    Finset.sum_range_succ,layout,q,key,value,Real.exp_log (by norm_num : (0 : ℝ) < 2)]

def inputs : List Scalar.Kind := [
  .read ⟨.global,320⟩ (Symbolic.encode .f32 1),
  .read ⟨.global,0⟩ (Symbolic.encode .f32 1),.read ⟨.global,64⟩ (Symbolic.encode .f32 0),
  .read ⟨.global,128⟩ (Symbolic.encode .f32 4),
  .read ⟨.global,0⟩ (Symbolic.encode .f32 1),.read ⟨.global,68⟩ (Symbolic.encode .f32 1),
  .read ⟨.global,132⟩ (Symbolic.encode .f32 10)]

theorem full_source_rescaling : ∃ final, Scalar.run ctx oracle code 105 {} =
    .ok (final,inputs ++ [.write ⟨.global,256⟩ (Symbolic.encode .f32 8)]) ∧
    final.core.thread.status = .done := by
  obtain ⟨final,hr,hf⟩ := complete_from_loop_entry layout ctx oracle q key value 0 0 1 (by decide)
    q_replies key_replies value_replies ready_inv
  rw [independent_output] at hr
  have he : Scalar.run ctx oracle code 68 ready = .ok (final,(inputs.drop 1) ++
      [.write ⟨.global,256⟩ (Symbolic.encode .f32 8)]) := by
    simpa [suffixReads,iterationReads,ScalarAttentionDot.loopReads,ScalarAttentionDot.reads,
      dotLayout,layout,q,key,value,inputs] using hr
  refine ⟨final,?_,hf⟩
  rw [show 105 = 37+68 by decide,Scalar.run_add,prefix_source]
  simp [he,Except.bind,inputs]

end
end Ptx.ScalarAttentionOuterTests
