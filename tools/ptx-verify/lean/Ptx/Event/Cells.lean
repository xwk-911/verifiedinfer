import Ptx.Event.Memory

/-! Representation between the baseline's optional u32 cells and byte maps.
An uninitialized cell imposes no byte value; a fixed fallback map supplies its
arbitrary but stable initial bytes. No initialization is invented by the relation.
-/
namespace Ptx.Event.Cells
open Ptx.ISA

def location (cell offset : Nat) : Location := ⟨.global, 4*cell+offset⟩
def wordByte (value offset : Nat) : Byte := ((encodeU32 value)[offset]?).getD (byte 0)

def Represents (cells : List (Option Nat)) (bytes : ByteMap) : Prop :=
  ∀ cell value, cells[cell]? = some (some value) →
    ∀ offset, offset < 4 → bytes (location cell offset) = wordByte value offset

def encode (cells : List (Option Nat)) (fallback : ByteMap) (loc : Location) : Byte :=
  if loc.space = .global then
    match cells[loc.address / 4]? with
    | some (some value) => wordByte value (loc.address % 4)
    | _ => fallback loc
  else fallback loc

theorem encode_represents (cells : List (Option Nat)) (fallback : ByteMap) :
    Represents cells (encode cells fallback) := by
  intro cell value hv offset ho
  have hdiv : (4*cell+offset)/4 = cell := by omega
  have hmod : (4*cell+offset)%4 = offset := by omega
  simp [encode,location,hdiv,hmod,hv]

theorem encode_of_representation {cells initial} (hr : Represents cells initial) :
    encode cells initial = initial := by
  funext loc
  by_cases hg : loc.space = .global
  · cases hv : cells[loc.address/4]? with
    | none => simp [encode,hg,hv]
    | some value =>
      cases value with
      | none => simp [encode,hg,hv]
      | some value =>
        have hoffset : loc.address % 4 < 4 := Nat.mod_lt _ (by decide)
        have he : location (loc.address/4) (loc.address%4) = loc := by
          rcases loc with ⟨space,address⟩
          simp only at hg
          subst space
          simp only [location,Location.mk.injEq,true_and]
          omega
        have hi := hr _ value hv _ hoffset
        rw [he] at hi
        simpa only [encode,ite_eq_left hg,hv] using hi.symm
  · simp [encode,hg]

theorem encode_uninitialized {cells fallback cell} (h : cells[cell]? = some none)
    (offset : Nat) (ho : offset < 4) : encode cells fallback (location cell offset) = fallback (location cell offset) := by
  have hdiv : (4*cell+offset)/4 = cell := by omega
  simp [encode,location,hdiv,h]

theorem encode_shared (cells : List (Option Nat)) (fallback : ByteMap) (cta : Dim3) (address : Nat) :
    encode cells fallback ⟨.shared cta,address⟩ = fallback ⟨.shared cta,address⟩ := by
  simp [encode]

theorem wordByte_payload (base : Location) (value offset : Nat) (ho : offset < 4) :
    payloadByte base (encodeU32 value) (base.add offset) = some (wordByte value offset) := by
  rw [payloadByte_offset]
  have hi : offset < (encodeU32 value).length := by simpa only [encodeU32_length] using ho
  rw [List.getElem?_eq_getElem hi]
  simp [wordByte,List.getElem?_eq_getElem hi]

theorem decode_wordBytes (value : Nat) :
    decodeLE [wordByte value 0,wordByte value 1,wordByte value 2,wordByte value 3] = value % 2^32 :=
  decode_encodeU32 value

end Ptx.Event.Cells
