import Ptx.Scalar.RealMath
import Ptx.Scalar.Memory

/-! Independent natural-exponential attention specification. The source's base-2
coefficient is related explicitly to alpha, without rounding log2(e) to a literal.
Empty key rows have the explicit convention output=0. No IEEE claim is made. -/
namespace Ptx.Attention
open Ptx.ISA Ptx.Scalar
open scoped BigOperators
noncomputable section

abbrev Matrix := Nat → Nat → ℝ
def dot (q key : Matrix) (row item : Nat) : Nat → ℝ
  | 0 => 0
  | count+1 => q row count*key item count+dot q key row item count
def score (q key : Matrix) (alpha : ℝ) (row item dim : Nat) : ℝ := alpha*dot q key row item dim
def denominator (q key : Matrix) (alpha : ℝ) (row keys dim : Nat) : ℝ :=
  ∑ item ∈ Finset.range keys, Real.exp (score q key alpha row item dim)
def numerator (q key value : Matrix) (alpha : ℝ) (row col keys dim : Nat) : ℝ :=
  ∑ item ∈ Finset.range keys, Real.exp (score q key alpha row item dim)*value item col
def output (q key value : Matrix) (alpha : ℝ) (row col keys dim : Nat) : ℝ :=
  if keys = 0 then 0 else numerator q key value alpha row col keys dim/denominator q key alpha row keys dim
def Post (q key value : Matrix) (alpha : ℝ) (rows keys dim base : Nat) (memory : Scalar.ByteMap) : Prop :=
  ∀ row col, row < rows → col < dim →
    RepresentsReal .f32 memory ⟨.global,base+4*(row*dim+col)⟩ (output q key value alpha row col keys dim)

theorem dot_congr {q key q' key' : Matrix} {row item row' item' count : Nat}
    (hq : ∀ k, k < count → q row k = q' row' k)
    (hk : ∀ k, k < count → key item k = key' item' k) :
    dot q key row item count = dot q' key' row' item' count := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [dot,hq n (by omega),hk n (by omega),ih (fun k h => hq k (by omega)) (fun k h => hk k (by omega))]

theorem denominator_pos (q key : Matrix) (alpha : ℝ) (row keys dim : Nat) (hn : 0 < keys) :
    0 < denominator q key alpha row keys dim := by
  apply Finset.sum_pos'
  · intro item _; exact (Real.exp_pos _).le
  · exact ⟨0,Finset.mem_range.mpr hn,Real.exp_pos _⟩

@[simp] theorem empty_output (q key value : Matrix) (alpha : ℝ) (row col dim : Nat) :
    output q key value alpha row col 0 dim = 0 := by simp [output]

end
end Ptx.Attention
