import Ptx.Ampere.MmaLayout
import Ptx.ISA.Fragments
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Reversible matrix/fragment assembly and exact-real m16n8k16 arithmetic.
This mathematical layer is not yet source/warp admission for mma.sync. In
particular no arbitrary oracle answer is accepted by calling it a collective.
-/
namespace Ptx.Ampere.Mma
noncomputable section

def gatherA {α : Type} (a : ACoord → α) : Lane × ASlot → α := fun p => a (aCoord p)
def gatherB {α : Type} (b : BCoord → α) : Lane × BSlot → α := fun p => b (bCoord p)
def gatherC {α : Type} (c : CCoord → α) : Lane × CSlot → α := fun p => c (cCoord p)
def scatterA {α : Type} (a : Lane × ASlot → α) : ACoord → α := fun p => a (aOwner p)
def scatterB {α : Type} (b : Lane × BSlot → α) : BCoord → α := fun p => b (bOwner p)
def scatterC {α : Type} (c : Lane × CSlot → α) : CCoord → α := fun p => c (cOwner p)

@[simp] theorem scatter_gather_a {α : Type} (a : ACoord → α) : scatterA (gatherA a) = a := by
  funext p
  simp only [scatterA,gatherA,a_coord_owner]
@[simp] theorem scatter_gather_b {α : Type} (b : BCoord → α) : scatterB (gatherB b) = b := by
  funext p
  simp only [scatterB,gatherB,b_coord_owner]
@[simp] theorem scatter_gather_c {α : Type} (c : CCoord → α) : scatterC (gatherC c) = c := by
  funext p
  simp only [scatterC,gatherC,c_coord_owner]
@[simp] theorem gather_scatter_a {α : Type} (a : Lane × ASlot → α) : gatherA (scatterA a) = a := by
  funext p
  simp only [scatterA,gatherA,a_owner_coord]
@[simp] theorem gather_scatter_b {α : Type} (b : Lane × BSlot → α) : gatherB (scatterB b) = b := by
  funext p
  simp only [scatterB,gatherB,b_owner_coord]
@[simp] theorem gather_scatter_c {α : Type} (c : Lane × CSlot → α) : gatherC (scatterC c) = c := by
  funext p
  simp only [scatterC,gatherC,c_owner_coord]

def matrixStep (a : ACoord → ℝ) (b : BCoord → ℝ) (c : CCoord → ℝ) (p : CCoord) : ℝ :=
  c p + ∑ k : Fin 16, a (p.1,k) * b (k,p.2)
def results (a : Lane × ASlot → ℝ) (b : Lane × BSlot → ℝ) (c : Lane × CSlot → ℝ) : Lane × CSlot → ℝ :=
  gatherC (matrixStep (scatterA a) (scatterB b) (scatterC c))
def Arithmetic (a : Lane × ASlot → ℝ) (b : Lane × BSlot → ℝ) (c d : Lane × CSlot → ℝ) : Prop :=
  ∀ p, d p = results a b c p

theorem results_gather (a : ACoord → ℝ) (b : BCoord → ℝ) (c : CCoord → ℝ) :
    results (gatherA a) (gatherB b) (gatherC c) = gatherC (matrixStep a b c) := by
  simp only [results,scatter_gather_a,scatter_gather_b,scatter_gather_c]
theorem arithmetic_correct {a : ACoord → ℝ} {b : BCoord → ℝ} {c : CCoord → ℝ} {d : Lane × CSlot → ℝ}
    (hd : Arithmetic (gatherA a) (gatherB b) (gatherC c) d) : scatterC d = matrixStep a b c := by
  have he : d = gatherC (matrixStep a b c) := (funext hd).trans (results_gather a b c)
  rw [he,scatter_gather_c]
theorem arithmetic_exists (a : Lane × ASlot → ℝ) (b : Lane × BSlot → ℝ) (c : Lane × CSlot → ℝ) :
    ∃ d, Arithmetic a b c d := ⟨results a b c,fun _ => rfl⟩

end
end Ptx.Ampere.Mma
