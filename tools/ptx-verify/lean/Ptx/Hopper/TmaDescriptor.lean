import Ptx.ISA.Fragments
import Ptx.ISA.Launch
import Mathlib.Data.Int.Basic

/-! Mathematical view of an unswizzled, non-interleaved, unit-stride 2-D tile
map with whole-byte elements and default byte-zero fill. The opaque CUDA tensor-map encoding is not decoded
here. Descriptor provenance/profile admission and runtime correspondence remain
separate from these address and byte-footprint definitions. -/
namespace Ptx.Hopper.Tma
open Ptx.ISA

inductive Proxy | generic | async | tensormap deriving Repr, DecidableEq
abbrev Descriptor2D := Ptx.ISA.TensorMap.Descriptor2D
structure Coordinates where
  x : Int
  y : Int
  deriving Repr, DecidableEq

def signed32 (n : Nat) : Int :=
  let bits : Nat := n % 2^32
  if bits < 2^31 then (bits : Int) else (bits : Int)-2^32

def Descriptor2D.bytes (d : Descriptor2D) : Nat := d.boxWidth*d.boxHeight*d.elementBytes

def Profile (d : Descriptor2D) : Prop :=
  0 < d.width ∧ d.width ≤ 2^32 ∧ 0 < d.height ∧ d.height ≤ 2^32 ∧
  0 < d.boxWidth ∧ d.boxWidth ≤ 256 ∧ 0 < d.boxHeight ∧ d.boxHeight ≤ 256 ∧
  (d.elementBytes = 1 ∨ d.elementBytes = 2 ∨ d.elementBytes = 4 ∨ d.elementBytes = 8 ∨ d.elementBytes = 16) ∧
  d.base < 2^64 ∧ d.base%16 = 0 ∧ d.rowStride < 2^40 ∧ d.rowStride%16 = 0 ∧
  (d.boxWidth*d.elementBytes)%16 = 0
instance (d) : Decidable (Profile d) := by unfold Profile; infer_instance

def xAt (d : Descriptor2D) (coords : Coordinates) (offset : Nat) : Int :=
  coords.x + ((offset/d.elementBytes)%d.boxWidth : Nat)
def yAt (d : Descriptor2D) (coords : Coordinates) (offset : Nat) : Int :=
  coords.y + (offset/d.elementBytes/d.boxWidth : Nat)
def InBounds (d : Descriptor2D) (coords : Coordinates) (offset : Nat) : Prop :=
  0 ≤ xAt d coords offset ∧ xAt d coords offset < (d.width : Int) ∧
  0 ≤ yAt d coords offset ∧ yAt d coords offset < (d.height : Int)
instance (d coords offset) : Decidable (InBounds d coords offset) := by unfold InBounds; infer_instance

/-- None within the destination footprint denotes an out-of-bounds source byte
which is zero-filled. Offsets outside the footprint also have no source access. -/
def sourceByte (d : Descriptor2D) (coords : Coordinates) (offset : Nat) : Option Location :=
  if offset < d.bytes ∧ InBounds d coords offset then
    some ⟨.global,d.base+(xAt d coords offset).toNat*d.elementBytes+
      (yAt d coords offset).toNat*d.rowStride+offset%d.elementBytes⟩
  else none

def byteValue (d : Descriptor2D) (coords : Coordinates) (initial : Location → Symbolic.Byte) (offset : Nat) : Symbolic.Byte :=
  match sourceByte d coords offset with | some location => initial location | none => .bits (byte 0)

theorem signed32_range (n : Nat) : -(2^31 : Int) ≤ signed32 n ∧ signed32 n < 2^31 := by
  have hm := Nat.mod_lt n (show 0 < 2^32 by decide)
  dsimp only [signed32]
  split_ifs <;> omega

theorem signed32_of_small {n : Nat} (hn : n < 2^31) : signed32 n = (n : Int) := by
  have hb : n < 2^32 := by omega
  dsimp only [signed32]
  rw [Nat.mod_eq_of_lt hb,if_pos hn]

theorem source_byte_some {d coords offset loc} (he : sourceByte d coords offset = some loc) :
    offset < d.bytes ∧ InBounds d coords offset ∧ loc.space = .global ∧
    loc.address = d.base+(xAt d coords offset).toNat*d.elementBytes+
      (yAt d coords offset).toNat*d.rowStride+offset%d.elementBytes := by
  unfold sourceByte at he
  split at he
  · rename_i hh
    cases he
    exact ⟨hh.1,hh.2,rfl,rfl⟩
  · cases he

theorem outside_footprint {d coords offset} (ho : d.bytes ≤ offset) : sourceByte d coords offset = none := by
  simp [sourceByte,Nat.not_lt.mpr ho]

theorem out_of_bounds_zero {d coords offset initial} (ho : ¬ InBounds d coords offset) :
    byteValue d coords initial offset = .bits (byte 0) := by simp [byteValue,sourceByte,ho]

theorem copied_byte {d coords offset initial loc} (hs : sourceByte d coords offset = some loc) :
    byteValue d coords initial offset = initial loc := by simp [byteValue,hs]

theorem source_in_global_span {d coords offset loc} (hb : 0 < d.elementBytes)
    (he : sourceByte d coords offset = some loc) :
    d.base ≤ loc.address ∧ loc.address < d.base+d.width*d.elementBytes+d.height*d.rowStride := by
  obtain ⟨_,hxy,_,haddr⟩ := source_byte_some he
  have hx : (xAt d coords offset).toNat < d.width := (Int.toNat_lt hxy.1).mpr hxy.2.1
  have hy : (yAt d coords offset).toNat < d.height := (Int.toNat_lt hxy.2.2.1).mpr hxy.2.2.2
  have hox := Nat.mod_lt offset hb
  have hxm := Nat.mul_le_mul_right d.elementBytes (Nat.succ_le_of_lt hx)
  have hym := Nat.mul_le_mul_right d.rowStride (Nat.le_of_lt hy)
  rw [Nat.succ_mul] at hxm
  omega

end Ptx.Hopper.Tma
