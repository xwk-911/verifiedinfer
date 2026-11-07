import Ptx.Hopper.TmaDescriptor
import Lean.Elab.Tactic.Omega

/-! Contiguous unswizzled rows of 128 f16 elements. The address result is
parameterized by base, height and byte offset; it is reused for A and B. -/
namespace Ptx.Hopper.Tma
open Ptx.ISA

theorem packed_rows_source_byte (base height offset : Nat) (ho : offset < 256*height) :
    sourceByte ⟨base,128,height,256,128,height,2⟩ ⟨0,0⟩ offset = some ⟨.global,base+offset⟩ := by
  have hx : offset/2%128 < 128 := Nat.mod_lt _ (by decide)
  have hy : offset/2/128 < height := by omega
  have hb : InBounds ⟨base,128,height,256,128,height,2⟩ ⟨0,0⟩ offset := by
    dsimp [InBounds,xAt,yAt]
    omega
  rw [sourceByte,if_pos ⟨by dsimp [Descriptor2D.bytes]; omega,hb⟩]
  simp only [xAt,yAt,Int.zero_add,Int.toNat_natCast]
  congr 2
  omega

end Ptx.Hopper.Tma
