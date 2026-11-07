import Ptx.Scalar.Memory
import Ptx.Event.Cells

/-! Integer words in the mixed symbolic memory. Integer byte fragments remain
distinct from exact-real float fragments; no bit reinterpretation is introduced. -/
namespace Ptx.Scalar
open Ptx.ISA Ptx.Event
noncomputable section

def u32Bytes (value : Nat) : List Symbolic.Byte := (encodeU32 value).map Symbolic.Byte.bits
def u32Byte (value offset : Nat) : Symbolic.Byte := .bits (Cells.wordByte value offset)
def RepresentsU32 (memory : ByteMap) (base : Location) (value : Nat) : Prop :=
  ∀ offset, offset < 4 → memory (base.add offset) = u32Byte value offset

theorem u32_bytes_size (value : Nat) : (u32Bytes value).length = 4 := by simp [u32Bytes]

theorem u32_payload_byte (base : Location) (value offset : Nat) (ho : offset < 4) :
    payloadByte base (u32Bytes value) (base.add offset) = some (u32Byte value offset) := by
  rw [payloadByte_offset]
  have hb : offset < (encodeU32 value).length := by simpa using ho
  simp [u32Bytes,u32Byte,Cells.wordByte,List.getElem?_eq_getElem hb]

theorem observe_u32_write {Answers : Type} {c : Event.Candidate Symbolic.Byte Answers}
    {initial rf co o writer base value}
    (hm : GenericMemoryConditions c initial rf co)
    (ho : ObserverConditions c initial rf co o)
    (hw : c.eventAt writer = some (.write base (u32Bytes value)))
    (hd : ∀ offset, offset < 4 → base.add offset ∈ o.domain)
    (he : ∀ offset, offset < 4 → ObserverEligible c rf (base.add offset))
    (hu : ∀ offset, offset < 4 → ∀ other v,
      c.writeByte other (base.add offset) = some v → other = writer) :
    RepresentsU32 o.output base value := by
  intro offset hb
  apply observer_unique_writer (writer := writer) hm ho (hd offset hb) (he offset hb)
  · simpa only [Candidate.writeByte,hw,Option.bind_some,Kind.writeByte] using u32_payload_byte base value offset hb
  · exact hu offset hb

theorem u32_bytes_injective {a b : Nat} (ha : a < 2^32) (hb : b < 2^32)
    (he : ∀ offset, offset < 4 → u32Byte a offset = u32Byte b offset) : a = b := by
  have hbytes : encodeU32 a = encodeU32 b := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have heq := Symbolic.Byte.bits.inj (he i (by simpa using hi))
      simpa [u32Byte,Cells.wordByte,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using heq
  have hd := congrArg decodeLE hbytes
  rw [decode_encodeU32,decode_encodeU32,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hd
  exact hd

theorem represented_u32_payload {initial base expected loc value}
    (hi : RepresentsU32 initial base expected)
    (hb : payloadByte base (u32Bytes expected) loc = some value) : initial loc = value := by
  have hh := payloadByte_bounds hb
  rw [u32_bytes_size] at hh
  let offset := loc.address-base.address
  have ho : offset < 4 := by dsimp [offset]; omega
  have hl : loc = base.add offset := by
    rcases loc with ⟨space,address⟩
    rcases base with ⟨baseSpace,baseAddress⟩
    simp only at hh
    simp only [Location.add,Location.mk.injEq]
    exact ⟨hh.1.symm,by dsimp [offset]; omega⟩
  rw [hl,u32_payload_byte base expected offset ho] at hb
  exact (hl ▸ hi offset ho).trans (Option.some.inj hb)

theorem immutable_u32_load {c : Candidate} {initial rf read base answer expected}
    (hm : ValueAgreement c initial (Eligible c rf) rf)
    (hr : c.eventAt read = some (.read base (u32Bytes answer)))
    (he : ∀ offset, offset < 4 → Eligible c rf read (base.add offset))
    (hn : ∀ offset, offset < 4 → ∀ writer, c.writeByte writer (base.add offset) = none)
    (hi : RepresentsU32 initial base expected) (ha : answer < 2^32) (hb : expected < 2^32) : answer = expected := by
  apply u32_bytes_injective ha hb
  intro offset ho
  have hread : c.readByte read (base.add offset) = some (u32Byte answer offset) := by
    simpa only [Candidate.readByte,hr,Option.bind_some,Kind.readByte] using u32_payload_byte base answer offset ho
  exact (unwritten_read_initial hm (he offset ho) hread (hn offset ho)).trans (hi offset ho)

end
end Ptx.Scalar
