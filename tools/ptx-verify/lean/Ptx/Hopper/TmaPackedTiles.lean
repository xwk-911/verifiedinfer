import Ptx.Hopper.TmaPackedRows

/-! Packed 128-f16-element rows, tiled along the tensor map's second
coordinate. This is an address theorem, independent of chosen data/RF and
reused for both A's eight-row tiles and B's one-row tiles. -/
namespace Ptx.Hopper.Tma
open Ptx.ISA

theorem packed_tile_source_byte (base rows tiles tile offset : Nat)
    (ht : tile < tiles) (ho : offset < 256*rows) :
    sourceByte ⟨base,128,rows*tiles,256,128,rows,2⟩ ⟨0,(rows*tile : Nat)⟩ offset =
      some ⟨.global,base+256*rows*tile+offset⟩ := by
  have hx : offset/2%128 < 128 := Nat.mod_lt _ (by decide)
  have hy : offset/2/128 < rows := by omega
  have hm : rows*(tile+1) ≤ rows*tiles := Nat.mul_le_mul_left rows (by omega)
  have hb : InBounds ⟨base,128,rows*tiles,256,128,rows,2⟩ ⟨0,(rows*tile : Nat)⟩ offset := by
    dsimp [InBounds,xAt,yAt]
    push_cast
    constructor
    · omega
    · constructor
      · omega
      · constructor
        · exact_mod_cast (Nat.zero_le (rows*tile+offset/2/128))
        · have hh : rows*tile+offset/2/128 < rows*tiles := by
            rw [Nat.mul_add,Nat.mul_one] at hm
            omega
          exact_mod_cast hh
  rw [sourceByte,if_pos ⟨by dsimp [Descriptor2D.bytes]; omega,hb⟩]
  simp only [xAt,yAt,Int.zero_add,← Int.natCast_add,Int.toNat_natCast]
  congr 2
  simp only [Nat.mul_assoc,Nat.add_mul]
  have hmul : rows*(tile*256) = 256*(rows*tile) := by
    rw [← Nat.mul_assoc,Nat.mul_comm (rows*tile)]
  omega

end Ptx.Hopper.Tma
