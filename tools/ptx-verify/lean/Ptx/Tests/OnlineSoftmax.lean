import Ptx.Kernels.ScalarAttentionUpdate

/-! Regression theorems for online attention and its actual translated blocks.
These are mathematical/local execution checks, not a global kernel contract. -/
namespace Ptx.OnlineSoftmaxTests
open Ptx.ISA Ptx.Scalar Ptx.Scalar.RealMath
noncomputable section

theorem source_typed : Scalar.ProgramTyped Generated.scalar_flash_attention.registerDeclarations
    Generated.scalar_flash_attention.parameters Generated.scalar_flash_attention.program :=
  Generated.scalar_flash_attention.checked.valid

theorem empty_row (score value : Nat → ℝ) : OnlineSoftmax.result score value 0 = 0 := rfl

theorem single_key (score value : Nat → ℝ) : OnlineSoftmax.result score value 1 = value 0 := by
  simp [OnlineSoftmax.result,OnlineSoftmax.run,OnlineSoftmax.initial]

theorem equal_scores (score : ℝ) (value : Nat → ℝ) :
    OnlineSoftmax.result (fun _ => score) value 2 = (value 0+value 1)/2 := by
  rw [OnlineSoftmax.result_correct]
  simp only [OnlineSoftmax.average,show (2 : Nat) ≠ 0 by decide,ite_false,
    OnlineSoftmax.numerator,OnlineSoftmax.denominator,Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  calc
    _ = (exp2 score*(value 0+value 1))/(exp2 score*2) := by congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ (exp2_ne_zero score)

def rescaled : OnlineSoftmax.State := OnlineSoftmax.update (OnlineSoftmax.initial 0 4) 1 10

/-- A new maximum rescales the old numerator and denominator; using the old
maximum, skipping rescaling or swapping the weighted operands changes this result. -/
theorem changed_maximum : rescaled.maximum = 1 ∧ rescaled.normalizer = 3/2 ∧
    rescaled.accumulator = 12 ∧ rescaled.accumulator/rescaled.normalizer = 8 := by
  norm_num [rescaled,OnlineSoftmax.update,OnlineSoftmax.initial]

theorem positive_divisor (score value : Nat → ℝ) {count : Nat} (hn : 0 < count) :
    (OnlineSoftmax.run score value count).normalizer ≠ 0 :=
  (OnlineSoftmax.run_normalizer_pos score value hn).ne'

def updateStart : Scalar.State := {
  core := {thread := {pc := 56},queries := 17}
  floats := [("%max",(.f32,0)),("%l",(.f32,1)),("%u",(.f32,4)),
    ("%score",(.f32,1)),("%vv",(.f32,10))]
}

theorem translated_rescaling (ctx : Scalar.Context) (oracle : Scalar.Oracle) :
    ∃ final, Scalar.run ctx oracle ScalarAttentionUpdate.code 9 updateStart = .ok (final,[]) ∧
      declarationLookup "%max" final.floats = some (.f32,1) ∧
      declarationLookup "%l" final.floats = some (.f32,3/2) ∧
      declarationLookup "%u" final.floats = some (.f32,12) ∧ final.core.queries = 17 := by
  let old := OnlineSoftmax.initial 0 4
  refine ⟨ScalarAttentionUpdate.afterUpdate updateStart old 1 10,
    ScalarAttentionUpdate.update_block ctx oracle updateStart old 1 10 rfl rfl ⟨rfl,rfl,rfl⟩ rfl rfl,?_,?_,?_,rfl⟩
  all_goals norm_num [ScalarAttentionUpdate.afterUpdate,old,OnlineSoftmax.initial]

def zeroDivision : List Scalar.Instr := [.divRn .f32 "%out" (.reg "%u") (.reg "%l")]
def zeroState : Scalar.State := {floats := [("%u",(.f32,7)),("%l",(.f32,0))]}

theorem zero_divisor_fault (ctx : Scalar.Context) (oracle : Scalar.Oracle) :
    Scalar.step ctx oracle zeroDivision zeroState = .error .zeroDivisor :=
  div_zero_rejected rfl rfl (by rfl) (by rfl)

theorem zero_divisor_has_no_success (ctx : Scalar.Context) (oracle : Scalar.Oracle) :
    ¬ ∃ final events, Scalar.step ctx oracle zeroDivision zeroState = .ok (final,events) := by
  rw [zero_divisor_fault]
  rintro ⟨_,_,h⟩; cases h

theorem independent_attention_spec (q key value : Attention.Matrix) (scale : ℝ) (row col keys dim : Nat) :
    OnlineSoftmax.result (fun item => scale*Attention.dot q key row item dim) (fun item => value item col) keys =
      Attention.output q key value (Real.log 2*scale) row col keys dim :=
  OnlineSoftmax.attention_correct q key value scale row col keys dim

def emptyContext : Scalar.Context := {
  id := ⟨.zero,⟨1,1,0⟩⟩
  block := ⟨2,2,1⟩
  params := [("Q",0),("K",64),("V",192),("O",128),("Scale",256),("M",2),("N",0),("D",3)]
}
def literalZero : ℝ := (F32Literal.mk 0 (by decide) (by decide)).value
def emptyFinal : Scalar.State := {
  core := {thread := {pc := 75,status := .done,regs := [
    ("%p",1),("%op",144),("%offset",4),("%col",1),("%tx",1),("%sx",2),("%bx",0),
    ("%row",1),("%ty",1),("%sy",2),("%by",0),("%d",3),("%n",0),("%m",2),
    ("%sp",256),("%o",128),("%vp",192),("%kr",64),("%q",0)]}}
  floats := [("%out",(.f32,literalZero))]
}

/-- Full actual-source entry-to-return regression: N=0 writes O[1,1]=0,
without reading Q/K/V/Scale or executing division, for EVERY reply oracle. -/
theorem empty_keys_source (oracle : Scalar.Oracle) :
    ∃ final, Scalar.run emptyContext oracle ScalarAttentionUpdate.code 32 {} =
      .ok (final,[.write ⟨.global,144⟩ (Symbolic.encode .f32 0)]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 0 := by
  have hr : Scalar.run emptyContext oracle ScalarAttentionUpdate.code 32 {} =
      .ok (emptyFinal,[.write ⟨.global,144⟩ (Symbolic.encode .f32 literalZero)]) := rfl
  exact ⟨emptyFinal,by simpa [literalZero] using hr,rfl,rfl⟩

def maskedRow : Scalar.Context := {emptyContext with params :=
  [("Q",0),("K",64),("V",192),("O",128),("Scale",256),("M",1),("N",7),("D",3)]}
def maskedCol : Scalar.Context := {emptyContext with params :=
  [("Q",0),("K",64),("V",192),("O",128),("Scale",256),("M",2),("N",7),("D",1)]}

theorem masked_row_source (oracle : Scalar.Oracle) :
    ((Scalar.run maskedRow oracle ScalarAttentionUpdate.code 21 {}).toOption.map
      (fun result => (result.1.core.thread.status,result.1.core.queries,result.2))) = some (.done,0,[]) := rfl

theorem masked_column_source (oracle : Scalar.Oracle) :
    ((Scalar.run maskedCol oracle ScalarAttentionUpdate.code 23 {}).toOption.map
      (fun result => (result.1.core.thread.status,result.1.core.queries,result.2))) = some (.done,0,[]) := rfl

end
end Ptx.OnlineSoftmaxTests
