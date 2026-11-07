import Ptx.Ampere.MmaLayout
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! Shared offsets for the 16x8x16 tiled source. These mathematical ownership
and fragment equations must still be connected to arbitrary actual source runs.
They do not assume any read value, synchronization or buffer-reuse safety. -/
namespace Ptx.Ampere.Tiled

abbrev X := Fin 4
abbrev Y := Fin 8
def lane (x : X) (y : Y) : Mma.Lane := ⟨x.val+4*y.val,by have := x.isLt; have := y.isLt; omega⟩
def copyBase (x : X) (y : Y) (part : Fin 3) : Nat := 256*part.val+32*y.val+8*x.val
def aRead (x : X) (y : Y) (reg : Fin 4) : Nat := 32*y.val+4*x.val+256*(reg.val%2)+16*(reg.val/2)
def bRead (x : X) (y : Y) (reg : Fin 2) : Nat := 512+32*y.val+4*x.val+16*reg.val
def aProducerX (x : X) (reg : Fin 4) : X := ⟨x.val/2+2*(reg.val/2),by have := x.isLt; have := reg.isLt; omega⟩
def aPart (reg : Fin 4) : Fin 3 := ⟨reg.val%2,by omega⟩
def bProducerX (x : X) (reg : Fin 2) : X := ⟨x.val/2+2*reg.val,by have := x.isLt; have := reg.isLt; omega⟩

theorem lane_x (x : X) (y : Y) : (lane x y).val%4 = x.val := by
  have := x.isLt
  simp only [lane]
  omega
theorem lane_y (x : X) (y : Y) : (lane x y).val/4 = y.val := by
  have := x.isLt
  simp only [lane]
  omega

theorem copy_bounds (x : X) (y : Y) (part : Fin 3) : copyBase x y part+8 ≤ 768 := by
  have := x.isLt
  have := y.isLt
  have := part.isLt
  simp only [copyBase]
  omega

theorem copy_byte_owner_unique {x x' : X} {y y' : Y} {part part' : Fin 3} {offset offset' : Fin 8}
    (he : copyBase x y part+offset.val = copyBase x' y' part'+offset'.val) :
    x = x' ∧ y = y' ∧ part = part' ∧ offset = offset' := by
  have := x.isLt
  have := x'.isLt
  have := y.isLt
  have := y'.isLt
  have := offset.isLt
  have := offset'.isLt
  simp only [copyBase] at he
  have hp : part.val = part'.val := by omega
  have hy : y.val = y'.val := by omega
  have hx : x.val = x'.val := by omega
  have ho : offset.val = offset'.val := by omega
  exact ⟨Fin.ext hx,Fin.ext hy,Fin.ext hp,Fin.ext ho⟩

theorem a_read_producer (x : X) (y : Y) (reg : Fin 4) :
    aRead x y reg = copyBase (aProducerX x reg) y (aPart reg)+4*(x.val%2) := by
  have := x.isLt
  simp only [aRead,copyBase,aProducerX,aPart]
  omega
theorem b_read_producer (x : X) (y : Y) (reg : Fin 2) :
    bRead x y reg = copyBase (bProducerX x reg) y 2+4*(x.val%2) := by
  have := x.isLt
  simp only [bRead,copyBase,bProducerX]
  omega

theorem producer_byte_offset (x : X) (offset : Fin 4) : 4*(x.val%2)+offset.val < 8 := by
  have := offset.isLt
  omega

theorem a_fragment_address (x : X) (y : Y) (reg : Fin 4) (half : Fin 2) :
    aRead x y reg+2*half.val =
      let slot : Mma.ASlot := ⟨2*reg.val+half.val,by have := reg.isLt; have := half.isLt; omega⟩
      2*(16*(Mma.aCoord (lane x y,slot)).1.val+(Mma.aCoord (lane x y,slot)).2.val) := by
  fin_cases reg <;> fin_cases half <;>
    simp [aRead,Mma.aCoord,lane_x,lane_y] <;> omega

theorem b_fragment_address (x : X) (y : Y) (reg : Fin 2) (half : Fin 2) :
    bRead x y reg+2*half.val =
      let slot : Mma.BSlot := ⟨2*reg.val+half.val,by have := reg.isLt; have := half.isLt; omega⟩
      512+2*(16*(Mma.bCoord (lane x y,slot)).2.val+(Mma.bCoord (lane x y,slot)).1.val) := by
  fin_cases reg <;> fin_cases half <;>
    simp [bRead,Mma.bCoord,lane_x,lane_y] <;> omega

end Ptx.Ampere.Tiled
