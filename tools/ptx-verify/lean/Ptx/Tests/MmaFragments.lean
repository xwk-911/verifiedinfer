import Ptx.Ampere.MmaPacked
import Ptx.Ampere.PackedF16
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Coverage and arithmetic regressions for the fragment layer only. These are
not native mma.sync executions or complete source/warp-matching witnesses. -/
namespace Ptx.MmaFragmentTests
open Ptx.Ampere Ptx.Ampere.Mma
noncomputable section

theorem a_high_k_low_row : aCoord (0,4) = (0,8) := by decide
theorem a_high_row_low_k : aCoord (0,2) = (8,0) := by decide
theorem b_high_k : bCoord (0,2) = (8,0) := by decide
theorem c_high_row : cCoord (0,2) = (8,0) := by decide
theorem final_a : aOwner (15,15) = (31,7) := by decide
theorem final_b : bOwner (15,7) = (31,3) := by decide
theorem final_c : cOwner (15,7) = (31,3) := by decide

def a : ACoord → ℝ := fun p => if p.1 = p.2 then 1 else 0
def b : BCoord → ℝ := fun p => 8*p.1.val+p.2.val
def c : CCoord → ℝ := fun p => 1000+p.1.val+p.2.val
theorem identity_product (p : CCoord) : matrixStep a b c p = c p+b (p.1,p.2) := by
  simp [matrixStep,a]
theorem sample_arithmetic : Arithmetic (gatherA a) (gatherB b) (gatherC c)
    (results (gatherA a) (gatherB b) (gatherC c)) := fun _ => rfl
theorem sample_result (p : CCoord) :
    scatterC (results (gatherA a) (gatherB b) (gatherC c)) p = c p+b (p.1,p.2) := by
  rw [arithmetic_correct sample_arithmetic]
  exact identity_product p
theorem sample_final_cell : scatterC (results (gatherA a) (gatherB b) (gatherC c)) (15,7) = 1149 := by
  rw [sample_result]
  norm_num [b,c]

def aLabels : ACoord → ℝ := fun p => 16*p.1.val+p.2.val
theorem second_a_register : (packA (gatherA aLabels) (0,1)).low = 128 ∧
    (packA (gatherA aLabels) (0,1)).high = 129 := by
  norm_num [packA,gatherA,aCoord,aLabels]
theorem third_a_register : (packA (gatherA aLabels) (0,2)).low = 8 ∧
    (packA (gatherA aLabels) (0,2)).high = 9 := by
  norm_num [packA,gatherA,aCoord,aLabels]
theorem second_b_register : (packB (gatherB b) (0,1)).low = 64 ∧
    (packB (gatherB b) (0,1)).high = 72 := by
  norm_num [packB,gatherB,bCoord,b]

theorem packed_size (x y : ℝ) : (PackedF16.mk x y).encode.length = 4 := PackedF16.encode_size _
theorem packed_roundtrip (x y : ℝ) : PackedF16.decode (PackedF16.mk x y).encode = some ⟨x,y⟩ :=
  PackedF16.decode_encode _
theorem integer_is_not_packed : PackedF16.decode ((Ptx.ISA.encodeU32 7).map Ptx.ISA.Symbolic.Byte.bits) = none :=
  PackedF16.integer_storage_rejected _
theorem swapped_halves_differ {x y : ℝ} (hn : x ≠ y) : (PackedF16.mk x y).encode ≠ (PackedF16.mk y x).encode := by
  intro he
  have hh := PackedF16.encode_injective he
  exact hn (congrArg PackedF16.low hh)

end
end Ptx.MmaFragmentTests
