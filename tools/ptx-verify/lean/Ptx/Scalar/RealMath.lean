import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

/-! Explicit exact-real abstraction of PTX ex2, matching the reference paper.
This is not the approximation, underflow/overflow or IEEE behavior of a GPU.
Finite f32 literal decoding remains separate and is never idealized here. -/
namespace Ptx.Scalar.RealMath
noncomputable section

def exp2 (x : ℝ) : ℝ := Real.exp (Real.log 2*x)

@[simp] theorem exp2_zero : exp2 0 = 1 := by simp [exp2]
@[simp] theorem exp2_one : exp2 1 = 2 := by simp [exp2,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
@[simp] theorem exp2_neg_one : exp2 (-1) = 1/2 := by
  simp [exp2,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
theorem exp2_pos (x : ℝ) : 0 < exp2 x := Real.exp_pos _
theorem exp2_ne_zero (x : ℝ) : exp2 x ≠ 0 := (exp2_pos x).ne'
theorem exp2_add (x y : ℝ) : exp2 (x+y) = exp2 x*exp2 y := by simp [exp2,mul_add,Real.exp_add]
theorem exp2_neg_cancel (x : ℝ) : exp2 (-x)*exp2 x = 1 := by rw [← exp2_add]; simp
theorem exp2_rescale (old next : ℝ) : exp2 (-old)*exp2 (old-next) = exp2 (-next) := by
  rw [← exp2_add]
  congr 1
  ring
theorem exp2_shift (x shift : ℝ) : exp2 (x-shift) = exp2 (-shift)*exp2 x := by
  rw [← exp2_add]
  congr 1
  ring
theorem exp2_scaled (scale x : ℝ) : exp2 (scale*x) = Real.exp ((Real.log 2*scale)*x) := by
  simp [exp2,mul_assoc]

end
end Ptx.Scalar.RealMath
