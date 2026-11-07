import Ptx.Ampere.MmaFragments
import Lean.Elab.Tactic.Omega

/-! m64n8k16 f32 accumulator ownership (PTX ISA 8.5 Figure 123).
All four warps contribute: a lane's first two values lie in its warp's
upper eight rows, its last two in the lower eight. This is a layout and
exact-real instruction layer, separate from source/memory/ISA admission. -/
namespace Ptx.Hopper.Wgmma
noncomputable section

abbrev Lane := Fin 128
abbrev Slot := Fin 4
abbrev ACoord := Fin 64 × Fin 16
abbrev BCoord := Fin 16 × Fin 8
abbrev CCoord := Fin 64 × Fin 8

def cCoord (p : Lane × Slot) : CCoord :=
  (⟨16*(p.1.val/32)+(p.1.val%32)/4+8*(p.2.val/2),by have := p.1.isLt; have := p.2.isLt; omega⟩,
   ⟨2*(p.1.val%4)+p.2.val%2,by have := p.1.isLt; have := p.2.isLt; omega⟩)
def cOwner (p : CCoord) : Lane × Slot :=
  (⟨32*(p.1.val/16)+4*(p.1.val%8)+p.2.val/2,by have := p.1.isLt; have := p.2.isLt; omega⟩,
   ⟨2*((p.1.val%16)/8)+p.2.val%2,by have := p.1.isLt; have := p.2.isLt; omega⟩)
theorem c_owner_coord (p : Lane × Slot) : cOwner (cCoord p) = p := by
  rcases p with ⟨lane,slot⟩
  apply Prod.ext <;> apply Fin.ext
  all_goals dsimp [cOwner,cCoord]; have := lane.isLt; have := slot.isLt; omega
theorem c_coord_owner (p : CCoord) : cCoord (cOwner p) = p := by
  rcases p with ⟨row,col⟩
  apply Prod.ext <;> apply Fin.ext
  all_goals dsimp [cOwner,cCoord]; have := row.isLt; have := col.isLt; omega
def cLayout : (Lane × Slot) ≃ CCoord := ⟨cCoord,cOwner,c_owner_coord,c_coord_owner⟩
theorem c_unique_owner {a b : Lane × Slot} (h : cCoord a = cCoord b) : a = b := cLayout.injective h
theorem c_covered (p : CCoord) : ∃ owner, cCoord owner = p := ⟨cOwner p,c_coord_owner p⟩

def gatherC {α : Type} (c : CCoord → α) : Lane × Slot → α := fun p => c (cCoord p)
def scatterC {α : Type} (c : Lane × Slot → α) : CCoord → α := fun p => c (cOwner p)
@[simp] theorem scatter_gather_c {α : Type} (c : CCoord → α) : scatterC (gatherC c) = c := by
  funext p
  simp only [scatterC,gatherC,c_coord_owner]
@[simp] theorem gather_scatter_c {α : Type} (c : Lane × Slot → α) : gatherC (scatterC c) = c := by
  funext p
  simp only [gatherC,scatterC,c_owner_coord]

def matrixStep (a : ACoord → ℝ) (b : BCoord → ℝ) (c : CCoord → ℝ) (p : CCoord) : ℝ :=
  c p + ∑ k : Fin 16, a (p.1,k)*b (k,p.2)
def results (a : ACoord → ℝ) (b : BCoord → ℝ) (c : Lane × Slot → ℝ) : Lane × Slot → ℝ :=
  gatherC (matrixStep a b (scatterC c))
def Arithmetic (a : ACoord → ℝ) (b : BCoord → ℝ) (c d : Lane × Slot → ℝ) : Prop :=
  ∀ p, d p = results a b c p
theorem arithmetic_exists (a : ACoord → ℝ) (b : BCoord → ℝ) (c : Lane × Slot → ℝ) :
    ∃ d, Arithmetic a b c d := ⟨results a b c,fun _ => rfl⟩
theorem arithmetic_correct {a b c d} (h : Arithmetic a b (gatherC c) d) : scatterC d = matrixStep a b c := by
  have he : d = gatherC (matrixStep a b c) := by
    simpa only [results,scatter_gather_c] using funext h
  rw [he,scatter_gather_c]

end
end Ptx.Hopper.Wgmma
