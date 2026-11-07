import Ptx.Kernels.CpAsyncCopySpec
import Ptx.Kernels.CpAsyncCopyMemory
import Ptx.Event.Publication

/-! Representation facts for constructing a payload from fixed initial words.
These facts do not assume memory consistency or the desired kernel output. -/
namespace Ptx.CpAsyncCopyGraph
open Ptx.ISA Ptx.Ampere Ptx.CpAsyncCopyTrace
noncomputable section

theorem payload_word_byte (values : Answers) (i : Fin 4) (offset : Nat) (ho : offset < 4) :
    (payload values)[4*i.val+offset]? = some (Scalar.u32Byte (word values i) offset) := by
  fin_cases i <;> interval_cases offset <;> rfl

theorem payload_word_read {values : Answers} {i : Fin 4} {loc value}
    (hr : Ptx.Event.payloadByte ⟨.shared .zero,4*i.val⟩ (Scalar.u32Bytes (word values i)) loc = some value) :
    Ptx.Event.payloadByte tile (payload values) loc = some value := by
  obtain ⟨offset,ho,rfl⟩ := Ptx.Event.payload_location hr
  rw [Scalar.u32_bytes_size] at ho
  have hv : Scalar.u32Byte (word values i) offset = value := by
    rw [Scalar.u32_payload_byte _ _ _ ho] at hr
    exact Option.some.inj hr
  have hp := payload_word_byte values i offset ho
  rw [hv] at hp
  have hloc : (⟨.shared .zero,4*i.val⟩ : Location).add offset = tile.add (4*i.val+offset) := by
    simp [Location.add,tile]
  rw [hloc,Ptx.Event.payloadByte_offset]
  exact hp

theorem represented_payload {src : Nat} {initial : Ptx.Event.ByteMap Symbolic.Byte} {values : Answers}
    (hi : ∀ i : Fin 4, values i < 2^32 ∧ Scalar.RepresentsU32 initial ⟨.global,src+4*i.val⟩ (values i))
    {loc value} (hp : Ptx.Event.payloadByte ⟨.global,src⟩ (payload values) loc = some value) :
    initial loc = value := by
  obtain ⟨offset,ho,rfl⟩ := Ptx.Event.payload_location hp
  rw [payload_size] at ho
  let i : Fin 4 := ⟨offset/4,by omega⟩
  have hrem : offset%4 < 4 := Nat.mod_lt _ (by decide)
  have hindex : 4*i.val+offset%4 = offset := by dsimp [i]; omega
  have hword : word values i = values i := Nat.mod_eq_of_lt (hi i).1
  rw [Ptx.Event.payloadByte_offset] at hp
  have hbyte := payload_word_byte values i (offset%4) hrem
  rw [hindex] at hbyte
  have hv : Scalar.u32Byte (values i) (offset%4) = value := by
    rw [hword] at hbyte
    exact Option.some.inj (hbyte.symm.trans hp)
  have hloc : (⟨.global,src⟩ : Location).add offset = (⟨.global,src+4*i.val⟩ : Location).add (offset%4) := by
    simp only [Location.add,Nat.add_assoc,hindex]
  rw [hloc]
  exact ((hi i).2 (offset%4) hrem).trans hv

theorem unique_writes {src dst bytes answers loc a b va vb}
    (ha : (graph src dst bytes answers).writeByte a loc = some va)
    (hb : (graph src dst bytes answers).writeByte b loc = some vb) : a = b := by
  rcases write_cases ha with ⟨rfl,hpa⟩ | ⟨i,rfl,hpa⟩ <;>
    rcases write_cases hb with ⟨rfl,hpb⟩ | ⟨j,rfl,hpb⟩
  · rfl
  · have h₁ := (Ptx.Event.payloadByte_bounds hpa).1
    have h₂ := (Ptx.Event.payloadByte_bounds hpb).1
    cases h₁.trans h₂.symm
  · have h₁ := (Ptx.Event.payloadByte_bounds hpa).1
    have h₂ := (Ptx.Event.payloadByte_bounds hpb).1
    cases h₁.trans h₂.symm
  · have h₁ := Ptx.Event.payloadByte_bounds hpa
    have h₂ := Ptx.Event.payloadByte_bounds hpb
    simp only [Scalar.u32_bytes_size] at h₁ h₂
    have he : i.val = j.val := by omega
    exact congrArg outputNode (Fin.ext he)

end
end Ptx.CpAsyncCopyGraph
