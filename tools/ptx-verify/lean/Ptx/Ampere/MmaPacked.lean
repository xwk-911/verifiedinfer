import Ptx.Ampere.MmaFragments
import Ptx.Ampere.PackedF16
import Mathlib.Tactic.FinCases

/-! Four A and two B logical f16 pairs per lane. These reversible packings
connect register-sized containers to the scalar-element fragment layouts.
They do not yet supply named register-bank/source/warp matching semantics.
-/
namespace Ptx.Ampere.Mma
noncomputable section

abbrev PackedA := Lane × Fin 4 → PackedF16
abbrev PackedB := Lane × Fin 2 → PackedF16

def packA (f : Lane × ASlot → ℝ) : PackedA := fun p =>
  ⟨f (p.1,⟨2*p.2.val,by have := p.2.isLt; omega⟩),f (p.1,⟨2*p.2.val+1,by have := p.2.isLt; omega⟩)⟩
def packB (f : Lane × BSlot → ℝ) : PackedB := fun p =>
  ⟨f (p.1,⟨2*p.2.val,by have := p.2.isLt; omega⟩),f (p.1,⟨2*p.2.val+1,by have := p.2.isLt; omega⟩)⟩
def unpackA (f : PackedA) : Lane × ASlot → ℝ := fun p =>
  let pair := f (p.1,⟨p.2.val/2,by have := p.2.isLt; omega⟩)
  if p.2.val%2 = 0 then pair.low else pair.high
def unpackB (f : PackedB) : Lane × BSlot → ℝ := fun p =>
  let pair := f (p.1,⟨p.2.val/2,by have := p.2.isLt; omega⟩)
  if p.2.val%2 = 0 then pair.low else pair.high

@[simp] theorem unpack_pack_a (f : Lane × ASlot → ℝ) : unpackA (packA f) = f := by
  funext ⟨lane,slot⟩
  fin_cases slot <;> simp [unpackA,packA,unpackB,packB]
@[simp] theorem unpack_pack_b (f : Lane × BSlot → ℝ) : unpackB (packB f) = f := by
  funext ⟨lane,slot⟩
  fin_cases slot <;> simp [unpackA,packA,unpackB,packB]
@[simp] theorem pack_unpack_a (f : PackedA) : packA (unpackA f) = f := by
  funext ⟨lane,reg⟩
  fin_cases reg <;> simp [packA,unpackA,packB,unpackB]
@[simp] theorem pack_unpack_b (f : PackedB) : packB (unpackB f) = f := by
  funext ⟨lane,reg⟩
  fin_cases reg <;> simp [packA,unpackA,packB,unpackB]

def packedResults (a : PackedA) (b : PackedB) (c : Lane × CSlot → ℝ) : Lane × CSlot → ℝ :=
  results (unpackA a) (unpackB b) c
theorem packed_results_gather (a : ACoord → ℝ) (b : BCoord → ℝ) (c : CCoord → ℝ) :
    packedResults (packA (gatherA a)) (packB (gatherB b)) (gatherC c) = gatherC (matrixStep a b c) := by
  simp only [packedResults,unpack_pack_a,unpack_pack_b,results_gather]

end
end Ptx.Ampere.Mma
