import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega

/-! The f16-input/f32-accumulator m16n8k16 fragment coordinates from
NVIDIA PTX ISA 9.5, section 9.7.16.5.8. Logical scalar elements are indexed
low half first within each packed register. No IEEE bit reinterpretation,
source instruction semantics or warp matching is supplied by this file.
-/
namespace Ptx.Ampere.Mma

abbrev Lane := Fin 32
abbrev ASlot := Fin 8
abbrev BSlot := Fin 4
abbrev CSlot := Fin 4
abbrev ACoord := Fin 16 × Fin 16
abbrev BCoord := Fin 16 × Fin 8
abbrev CCoord := Fin 16 × Fin 8

def aCoord (p : Lane × ASlot) : ACoord :=
  (⟨p.1.val/4 + 8*((p.2.val/2)%2),by have := p.1.isLt; have := p.2.isLt; omega⟩,
   ⟨2*(p.1.val%4) + p.2.val%2 + 8*(p.2.val/4),by have := p.1.isLt; have := p.2.isLt; omega⟩)
def aOwner (p : ACoord) : Lane × ASlot :=
  (⟨4*(p.1.val%8) + (p.2.val%8)/2,by have := p.1.isLt; have := p.2.isLt; omega⟩,
   ⟨4*(p.2.val/8) + 2*(p.1.val/8) + p.2.val%2,by have := p.1.isLt; have := p.2.isLt; omega⟩)

def bCoord (p : Lane × BSlot) : BCoord :=
  (⟨2*(p.1.val%4) + p.2.val%2 + 8*(p.2.val/2),by have := p.1.isLt; have := p.2.isLt; omega⟩,
   ⟨p.1.val/4,by have := p.1.isLt; omega⟩)
def bOwner (p : BCoord) : Lane × BSlot :=
  (⟨4*p.2.val + (p.1.val%8)/2,by have := p.1.isLt; have := p.2.isLt; omega⟩,
   ⟨2*(p.1.val/8) + p.1.val%2,by have := p.1.isLt; omega⟩)

def cCoord (p : Lane × CSlot) : CCoord :=
  (⟨p.1.val/4 + 8*(p.2.val/2),by have := p.1.isLt; have := p.2.isLt; omega⟩,
   ⟨2*(p.1.val%4) + p.2.val%2,by have := p.1.isLt; have := p.2.isLt; omega⟩)
def cOwner (p : CCoord) : Lane × CSlot :=
  (⟨4*(p.1.val%8) + p.2.val/2,by have := p.1.isLt; have := p.2.isLt; omega⟩,
   ⟨2*(p.1.val/8) + p.2.val%2,by have := p.1.isLt; omega⟩)

theorem a_owner_coord (p : Lane × ASlot) : aOwner (aCoord p) = p := by
  rcases p with ⟨lane,slot⟩
  apply Prod.ext <;> apply Fin.ext
  all_goals dsimp [aOwner,aCoord]; have := lane.isLt; have := slot.isLt; omega
theorem a_coord_owner (p : ACoord) : aCoord (aOwner p) = p := by
  rcases p with ⟨row,col⟩
  apply Prod.ext <;> apply Fin.ext
  all_goals dsimp [aOwner,aCoord]; have := row.isLt; have := col.isLt; omega
theorem b_owner_coord (p : Lane × BSlot) : bOwner (bCoord p) = p := by
  rcases p with ⟨lane,slot⟩
  apply Prod.ext <;> apply Fin.ext
  all_goals dsimp [bOwner,bCoord]; have := lane.isLt; have := slot.isLt; omega
theorem b_coord_owner (p : BCoord) : bCoord (bOwner p) = p := by
  rcases p with ⟨row,col⟩
  apply Prod.ext <;> apply Fin.ext
  all_goals dsimp [bOwner,bCoord]; have := row.isLt; have := col.isLt; omega
theorem c_owner_coord (p : Lane × CSlot) : cOwner (cCoord p) = p := by
  rcases p with ⟨lane,slot⟩
  apply Prod.ext <;> apply Fin.ext
  all_goals dsimp [cOwner,cCoord]; have := lane.isLt; have := slot.isLt; omega
theorem c_coord_owner (p : CCoord) : cCoord (cOwner p) = p := by
  rcases p with ⟨row,col⟩
  apply Prod.ext <;> apply Fin.ext
  all_goals dsimp [cOwner,cCoord]; have := row.isLt; have := col.isLt; omega

def aLayout : (Lane × ASlot) ≃ ACoord := ⟨aCoord,aOwner,a_owner_coord,a_coord_owner⟩
def bLayout : (Lane × BSlot) ≃ BCoord := ⟨bCoord,bOwner,b_owner_coord,b_coord_owner⟩
def cLayout : (Lane × CSlot) ≃ CCoord := ⟨cCoord,cOwner,c_owner_coord,c_coord_owner⟩

/-- A missing lane omits its elements; a duplicated owner cannot represent a
second matrix element. These statements concern fragment layout, not scheduling. -/
theorem a_unique_owner {a b : Lane × ASlot} (he : aCoord a = aCoord b) : a = b := aLayout.injective he
theorem b_unique_owner {a b : Lane × BSlot} (he : bCoord a = bCoord b) : a = b := bLayout.injective he
theorem c_unique_owner {a b : Lane × CSlot} (he : cCoord a = cCoord b) : a = b := cLayout.injective he

end Ptx.Ampere.Mma
