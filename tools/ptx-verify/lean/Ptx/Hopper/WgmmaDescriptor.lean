import Ptx.Hopper.WgmmaLayout
import Ptx.ISA.Launch

/-! Exact no-swizzle WGMMA descriptor fields, distinct from opaque TMA tensor
maps. Units are 16 bytes; reserved/swizzle/base bits are rejected by canonical
re-encoding. Address functions expose general core strides; Packed selects a
specific contiguous-core profile with leading=128 and stride=256 bytes.
The profile is a supported-layout restriction, not a complete ISA UB test.
Allocation bounds, lifetime, proxy agreement and device conformance are separate.
Basis: PTX ISA 8.5 Figures 131/132/142/143 and Matrix Descriptor Format;
NVIDIA CUTLASS Major-K INTERLEAVE canonical layout provides a cross-check. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA

structure MatrixDescriptor where
  start : Fin 16384
  leading : Fin 16384
  stride : Fin 16384
  deriving Repr, DecidableEq
def MatrixDescriptor.decode (raw : Nat) : MatrixDescriptor :=
  ⟨⟨raw%16384,Nat.mod_lt _ (by decide)⟩,
   ⟨(raw/65536)%16384,Nat.mod_lt _ (by decide)⟩,
   ⟨(raw/4294967296)%16384,Nat.mod_lt _ (by decide)⟩⟩
def MatrixDescriptor.encode (d : MatrixDescriptor) : Nat :=
  d.start.val+65536*d.leading.val+4294967296*d.stride.val
def MatrixDescriptor.base (d : MatrixDescriptor) : Nat := 16*d.start.val
def MatrixDescriptor.leadingBytes (d : MatrixDescriptor) : Nat := 16*d.leading.val
def MatrixDescriptor.strideBytes (d : MatrixDescriptor) : Nat := 16*d.stride.val
def MatrixDescriptor.Canonical (raw : Nat) : Prop := raw = (decode raw).encode
def MatrixDescriptor.Packed (raw : Nat) : Prop :=
  Canonical raw ∧ (decode raw).leading.val = 8 ∧ (decode raw).stride.val = 16
instance (raw) : Decidable (MatrixDescriptor.Canonical raw) := inferInstanceAs (Decidable (raw = (MatrixDescriptor.decode raw).encode))
instance (raw) : Decidable (MatrixDescriptor.Packed raw) := by unfold MatrixDescriptor.Packed; infer_instance

theorem descriptor_decode_encode (d : MatrixDescriptor) : MatrixDescriptor.decode d.encode = d := by
  rcases d with ⟨start,leading,stride⟩
  unfold MatrixDescriptor.encode MatrixDescriptor.decode
  congr 1 <;> apply Fin.ext
  all_goals dsimp; have := start.isLt; have := leading.isLt; have := stride.isLt; omega
theorem descriptor_encoded_canonical (d : MatrixDescriptor) : MatrixDescriptor.Canonical d.encode := by
  simp only [MatrixDescriptor.Canonical,descriptor_decode_encode]
theorem descriptor_canonical_bounded {raw} (h : MatrixDescriptor.Canonical raw) : raw < 2^46 := by
  rw [h]
  have h0 := (MatrixDescriptor.decode raw).start.isLt
  have h1 := (MatrixDescriptor.decode raw).leading.isLt
  have h2 := (MatrixDescriptor.decode raw).stride.isLt
  dsimp [MatrixDescriptor.encode]
  omega

def aAddress (d : MatrixDescriptor) (p : ACoord) (byte : Fin 2) : Nat :=
  d.base+(p.1.val/8)*d.strideBytes+(p.2.val/8)*d.leadingBytes+16*(p.1.val%8)+2*(p.2.val%8)+byte.val
def bAddress (d : MatrixDescriptor) (p : BCoord) (byte : Fin 2) : Nat :=
  d.base+(p.2.val/8)*d.strideBytes+(p.1.val/8)*d.leadingBytes+16*(p.2.val%8)+2*(p.1.val%8)+byte.val
def aOffset (p : ACoord × Fin 2) : Fin 2048 :=
  ⟨256*(p.1.1.val/8)+128*(p.1.2.val/8)+16*(p.1.1.val%8)+2*(p.1.2.val%8)+p.2.val,
    by have := p.1.1.isLt; have := p.1.2.isLt; have := p.2.isLt; omega⟩
def bOffset (p : BCoord × Fin 2) : Fin 256 :=
  ⟨128*(p.1.1.val/8)+16*p.1.2.val+2*(p.1.1.val%8)+p.2.val,
    by have := p.1.1.isLt; have := p.1.2.isLt; have := p.2.isLt; omega⟩
def aByteOwner (offset : Fin 2048) : ACoord × Fin 2 :=
  ((⟨8*(offset.val/256)+(offset.val%128)/16,by have := offset.isLt; omega⟩,
    ⟨8*((offset.val%256)/128)+(offset.val%16)/2,by have := offset.isLt; omega⟩),
    ⟨offset.val%2,Nat.mod_lt _ (by decide)⟩)
def bByteOwner (offset : Fin 256) : BCoord × Fin 2 :=
  ((⟨8*(offset.val/128)+(offset.val%16)/2,by have := offset.isLt; omega⟩,
    ⟨(offset.val%128)/16,by have := offset.isLt; omega⟩),
    ⟨offset.val%2,Nat.mod_lt _ (by decide)⟩)
theorem a_offset_owner (offset : Fin 2048) : aOffset (aByteOwner offset) = offset := by
  apply Fin.ext
  dsimp [aOffset,aByteOwner]
  have := offset.isLt
  omega
theorem b_offset_owner (offset : Fin 256) : bOffset (bByteOwner offset) = offset := by
  apply Fin.ext
  dsimp [bOffset,bByteOwner]
  have := offset.isLt
  omega
theorem a_owner_offset (p : ACoord × Fin 2) : aByteOwner (aOffset p) = p := by
  rcases p with ⟨⟨row,col⟩,byte⟩
  apply Prod.ext
  · apply Prod.ext <;> apply Fin.ext
    all_goals dsimp [aByteOwner,aOffset]; have := row.isLt; have := col.isLt; have := byte.isLt; omega
  · apply Fin.ext
    dsimp [aByteOwner,aOffset]; have := row.isLt; have := col.isLt; have := byte.isLt; omega
theorem b_owner_offset (p : BCoord × Fin 2) : bByteOwner (bOffset p) = p := by
  rcases p with ⟨⟨row,col⟩,byte⟩
  apply Prod.ext
  · apply Prod.ext <;> apply Fin.ext
    all_goals dsimp [bByteOwner,bOffset]; have := row.isLt; have := col.isLt; have := byte.isLt; omega
  · apply Fin.ext
    dsimp [bByteOwner,bOffset]; have := row.isLt; have := col.isLt; have := byte.isLt; omega
def aByteLayout : (ACoord × Fin 2) ≃ Fin 2048 := ⟨aOffset,aByteOwner,a_owner_offset,a_offset_owner⟩
def bByteLayout : (BCoord × Fin 2) ≃ Fin 256 := ⟨bOffset,bByteOwner,b_owner_offset,b_offset_owner⟩
theorem packed_a_address {raw} (h : MatrixDescriptor.Packed raw) (p : ACoord) (byte : Fin 2) :
    aAddress (MatrixDescriptor.decode raw) p byte = (MatrixDescriptor.decode raw).base+(aOffset (p,byte)).val := by
  dsimp [aAddress,MatrixDescriptor.strideBytes,MatrixDescriptor.leadingBytes,aOffset]
  rw [h.2.1,h.2.2]
  omega
theorem packed_b_address {raw} (h : MatrixDescriptor.Packed raw) (p : BCoord) (byte : Fin 2) :
    bAddress (MatrixDescriptor.decode raw) p byte = (MatrixDescriptor.decode raw).base+(bOffset (p,byte)).val := by
  dsimp [bAddress,MatrixDescriptor.strideBytes,MatrixDescriptor.leadingBytes,bOffset]
  rw [h.2.1,h.2.2]
  have hh : p.2.val/8 = 0 := Nat.div_eq_of_lt p.2.isLt
  rw [hh]
  omega
theorem packed_a_unique {raw} (h : MatrixDescriptor.Packed raw) {p q : ACoord × Fin 2}
    (he : aAddress (MatrixDescriptor.decode raw) p.1 p.2 = aAddress (MatrixDescriptor.decode raw) q.1 q.2) : p = q := by
  rw [packed_a_address h,packed_a_address h] at he
  apply aByteLayout.injective
  apply Fin.ext
  change (aOffset p).val = (aOffset q).val
  exact Nat.add_left_cancel he
theorem packed_b_unique {raw} (h : MatrixDescriptor.Packed raw) {p q : BCoord × Fin 2}
    (he : bAddress (MatrixDescriptor.decode raw) p.1 p.2 = bAddress (MatrixDescriptor.decode raw) q.1 q.2) : p = q := by
  rw [packed_b_address h,packed_b_address h] at he
  apply bByteLayout.injective
  apply Fin.ext
  change (bOffset p).val = (bOffset q).val
  exact Nat.add_left_cancel he

end Ptx.Hopper.Wgmma
