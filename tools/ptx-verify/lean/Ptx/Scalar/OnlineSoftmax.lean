import Ptx.Kernels.AttentionSpec

/-! A reusable rescaled prefix-sum invariant for online attention. Initialization
uses the first finite score, avoiding a negative-infinity sentinel. The invariant
does not assume correct memory reads or PTX execution; those are later duties. -/
namespace Ptx.Scalar.OnlineSoftmax
open Ptx.Scalar.RealMath
open scoped BigOperators
noncomputable section

def denominator (score : Nat → ℝ) (count : Nat) : ℝ := ∑ item ∈ Finset.range count, exp2 (score item)
def numerator (score value : Nat → ℝ) (count : Nat) : ℝ := ∑ item ∈ Finset.range count, exp2 (score item)*value item
def average (score value : Nat → ℝ) (count : Nat) : ℝ :=
  if count = 0 then 0 else numerator score value count/denominator score count

theorem average_congr {score value score' value' : Nat → ℝ} {count : Nat}
    (hs : ∀ j, j < count → score j = score' j) (hv : ∀ j, j < count → value j = value' j) :
    average score value count = average score' value' count := by
  have hnum : numerator score value count = numerator score' value' count := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j (Finset.mem_range.mp hj),hv j (Finset.mem_range.mp hj)]
  have hden : denominator score count = denominator score' count := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j (Finset.mem_range.mp hj)]
  simp only [average,hnum,hden]

structure State where
  maximum : ℝ
  normalizer : ℝ
  accumulator : ℝ

def initial (score value : ℝ) : State := ⟨score,1,value⟩
def update (s : State) (score value : ℝ) : State :=
  let next := max s.maximum score
  let rescale := exp2 (s.maximum-next)
  let weight := exp2 (score-next)
  ⟨next,s.normalizer*rescale+weight,s.accumulator*rescale+weight*value⟩
def Inv (score value : Nat → ℝ) (count : Nat) (s : State) : Prop :=
  s.normalizer = exp2 (-s.maximum)*denominator score count ∧
  s.accumulator = exp2 (-s.maximum)*numerator score value count

theorem denominator_succ (score : Nat → ℝ) (count : Nat) :
    denominator score (count+1) = denominator score count+exp2 (score count) := by
  exact Finset.sum_range_succ _ _
theorem numerator_succ (score value : Nat → ℝ) (count : Nat) :
    numerator score value (count+1) = numerator score value count+exp2 (score count)*value count := by
  exact Finset.sum_range_succ _ _
theorem denominator_pos (score : Nat → ℝ) {count : Nat} (hn : 0 < count) : 0 < denominator score count := by
  apply Finset.sum_pos'
  · intro item _; exact (exp2_pos _).le
  · exact ⟨0,Finset.mem_range.mpr hn,exp2_pos _⟩

theorem initial_inv (score value : Nat → ℝ) : Inv score value 1 (initial (score 0) (value 0)) := by
  constructor
  · simpa only [initial,denominator,Finset.sum_range_one] using (exp2_neg_cancel (score 0)).symm
  · simp only [initial,numerator,Finset.sum_range_one]
    rw [← mul_assoc,exp2_neg_cancel,one_mul]

theorem update_inv {score value count s} (hi : Inv score value count s) :
    Inv score value (count+1) (update s (score count) (value count)) := by
  let next := max s.maximum (score count)
  have hw := exp2_shift (score count) next
  constructor
  · change s.normalizer*exp2 (s.maximum-next)+exp2 (score count-next) = _
    rw [hi.1,denominator_succ]
    change (exp2 (-s.maximum)*denominator score count)*exp2 (s.maximum-next)+exp2 (score count-next) =
      exp2 (-next)*(denominator score count+exp2 (score count))
    calc
      _ = (exp2 (-s.maximum)*exp2 (s.maximum-next))*denominator score count+exp2 (-next)*exp2 (score count) := by rw [hw]; ring
      _ = _ := by rw [exp2_rescale]; ring
  · change s.accumulator*exp2 (s.maximum-next)+exp2 (score count-next)*value count = _
    rw [hi.2,numerator_succ]
    change (exp2 (-s.maximum)*numerator score value count)*exp2 (s.maximum-next)+exp2 (score count-next)*value count =
      exp2 (-next)*(numerator score value count+exp2 (score count)*value count)
    calc
      _ = (exp2 (-s.maximum)*exp2 (s.maximum-next))*numerator score value count+exp2 (-next)*exp2 (score count)*value count := by rw [hw]; ring
      _ = _ := by rw [exp2_rescale]; ring

theorem normalizer_pos {score value count s} (hi : Inv score value count s) (hn : 0 < count) : 0 < s.normalizer := by
  rw [hi.1]
  exact mul_pos (exp2_pos _) (denominator_pos score hn)

theorem normalized {score value count s} (hi : Inv score value count s) :
    s.accumulator/s.normalizer = numerator score value count/denominator score count := by
  rw [hi.1,hi.2]
  exact mul_div_mul_left _ _ (exp2_ne_zero _)

def run (score value : Nat → ℝ) : Nat → State
  | 0 => ⟨0,0,0⟩
  | count+1 => if count = 0 then initial (score 0) (value 0) else update (run score value count) (score count) (value count)
def result (score value : Nat → ℝ) (count : Nat) : ℝ :=
  if count = 0 then 0 else (run score value count).accumulator/(run score value count).normalizer

theorem run_inv (score value : Nat → ℝ) (count : Nat) : Inv score value count (run score value count) := by
  induction count with
  | zero => simp [run,Inv,denominator,numerator]
  | succ count ih =>
    by_cases hc : count = 0
    · subst count; exact initial_inv score value
    · simpa only [run,ite_eq_right hc] using update_inv ih

theorem run_normalizer_pos (score value : Nat → ℝ) {count : Nat} (hn : 0 < count) :
    0 < (run score value count).normalizer := normalizer_pos (run_inv score value count) hn

theorem result_correct (score value : Nat → ℝ) (count : Nat) : result score value count = average score value count := by
  unfold result average
  split
  · rfl
  · exact normalized (run_inv score value count)

theorem update_shifts_nonpos (s : State) (score value : ℝ) :
    s.maximum-(update s score value).maximum ≤ 0 ∧ score-(update s score value).maximum ≤ 0 :=
  ⟨sub_nonpos.mpr (le_max_left _ _),sub_nonpos.mpr (le_max_right _ _)⟩

theorem attention_bridge (q key value : Attention.Matrix) (scale : ℝ) (row col keys dim : Nat) :
    average (fun item => scale*Attention.dot q key row item dim) (fun item => value item col) keys =
      Attention.output q key value (Real.log 2*scale) row col keys dim := by
  simp [average,Attention.output,numerator,denominator,Attention.numerator,Attention.denominator,Attention.score,exp2_scaled]

theorem attention_correct (q key value : Attention.Matrix) (scale : ℝ) (row col keys dim : Nat) :
    result (fun item => scale*Attention.dot q key row item dim) (fun item => value item col) keys =
      Attention.output q key value (Real.log 2*scale) row col keys dim := by
  rw [result_correct,attention_bridge]

end
end Ptx.Scalar.OnlineSoftmax
