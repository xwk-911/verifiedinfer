import Ptx.Kernels.HopperDoubleBufferSpec
import Mathlib.Algebra.BigOperators.Intervals

/-! Relate tiled accumulation to an ordinary matrix-product specification
whose inner dimension is 16*T. This algebraic bridge does not assume an
execution result and does not establish the generated source's loop invariant.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section

def tileA (a : Fin 64 × Nat → ℝ) (tile : Nat) (p : Wgmma.ACoord) : ℝ := a (p.1,16*tile+p.2.val)
def tileB (b : Nat × Fin 8 → ℝ) (tile : Nat) (p : Wgmma.BCoord) : ℝ := b (16*tile+p.1.val,p.2)
def matmul (a : Fin 64 × Nat → ℝ) (b : Nat × Fin 8 → ℝ) (tiles : Nat) (p : Wgmma.CCoord) : ℝ :=
  ∑ k ∈ Finset.range (16*tiles), a (p.1,k)*b (k,p.2)

theorem result_is_matmul (a b tiles p) : result (tileA a) (tileB b) tiles p = matmul a b tiles p := by
  induction tiles with
  | zero => simp [result,matmul]
  | succ n ih =>
    rw [result,Wgmma.matrixStep,ih]
    simp only [matmul,Nat.mul_succ,Finset.sum_range_add]
    congr 1
theorem specification_is_matmul (a b tiles p) : specification (tileA a) (tileB b) tiles p = matmul a b tiles p :=
  (result_matches_specification _ _ _ _).symm.trans (result_is_matmul a b tiles p)

end
end Ptx.Kernels.HopperDoubleBuffer
