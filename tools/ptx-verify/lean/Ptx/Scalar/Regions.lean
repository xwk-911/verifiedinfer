import Ptx.Scalar.Memory

/-! Byte-region arithmetic for four-fragment scalar words. Region separation
permits an empty input region at any address. These facts do not assert physical
allocation or replace event provenance/consistency obligations. -/
namespace Ptx.Scalar
open Ptx.ISA Ptx.Event
noncomputable section

def InWords (base count : Nat) (loc : Location) : Prop :=
  loc.space = .global ∧ base ≤ loc.address ∧ loc.address < base+4*count

def WordsDisjoint (a countA b countB : Nat) : Prop :=
  countA = 0 ∨ countB = 0 ∨ a+4*countA ≤ b ∨ b+4*countB ≤ a

instance instDecidableWordsDisjoint (a countA b countB : Nat) : Decidable (WordsDisjoint a countA b countB) :=
  inferInstanceAs (Decidable (countA = 0 ∨ countB = 0 ∨ a+4*countA ≤ b ∨ b+4*countB ≤ a))

theorem words_disjoint {a countA b countB loc}
    (hd : WordsDisjoint a countA b countB) (ha : InWords a countA loc) (hb : InWords b countB loc) : False := by
  unfold WordsDisjoint at hd
  unfold InWords at ha hb
  rcases hd with h | h | h | h <;> omega

theorem matrix_index_lt {r c m n : Nat} (hr : r < m) (hc : c < n) : r*n+c < m*n := by
  have hm := Nat.mul_le_mul_right n (by omega : r+1 ≤ m)
  have hh := Nat.add_lt_add_left hc (r*n)
  simp only [Nat.add_mul,Nat.one_mul] at hm
  omega

theorem word_in_region {base count index address : Nat} (hi : index < count)
    (hlo : base+4*index ≤ address) (hhi : address < base+4*index+4) :
    InWords base count ⟨.global,address⟩ := by
  change (.global : AddressSpace) = .global ∧ base ≤ address ∧ address < base+4*count
  exact ⟨rfl,by omega,by omega⟩

theorem word_payload_in_region {base count index : Nat} {bytes : List Symbolic.Byte}
    {loc : Location} {value : Symbolic.Byte} (hi : index < count) (hs : bytes.length = 4)
    (hp : payloadByte ⟨.global,base+4*index⟩ bytes loc = some value) :
    InWords base count loc := by
  have hb := payloadByte_bounds hp
  rw [hs] at hb
  dsimp only at hb
  exact ⟨hb.1.symm,by omega,by omega⟩

theorem encoded_in_region {base count index : Nat} {value : ℝ} {loc : Location} {byte : Symbolic.Byte}
    (hi : index < count)
    (hp : payloadByte ⟨.global,base+4*index⟩ (Symbolic.encode .f32 value) loc = some byte) :
    InWords base count loc := by
  have hb := payloadByte_bounds hp
  simp only [Symbolic.encode_length,Symbolic.Format.bytes] at hb
  exact ⟨hb.1.symm,by omega,by omega⟩

theorem word_base_in_region {base count index : Nat} (hi : index < count) :
    InWords base count ⟨.global,base+4*index⟩ :=
  word_in_region hi (Nat.le_refl _) (by omega)

theorem word_index_of_overlap {base i j address : Nat}
    (ha : base+4*i ≤ address) (hb : address < base+4*i+4)
    (hc : base+4*j ≤ address) (hd : address < base+4*j+4) : i = j := by omega

theorem word_region_offset {base : Nat} {loc : Location} (hl : InWords base 1 loc) :
    ∃ offset, offset < 4 ∧ loc = (⟨.global,base⟩ : Location).add offset := by
  let offset := loc.address-base
  have ho : offset < 4 := by unfold InWords at hl; dsimp [offset]; omega
  refine ⟨offset,ho,?_⟩
  rcases loc with ⟨space,address⟩
  have hs : space = .global := hl.1
  subst space
  simp only [Location.add,Location.mk.injEq,true_and]
  dsimp [offset]
  have hh := hl.2.1
  simp only at hh
  omega

end
end Ptx.Scalar
