import Ptx.ISA.Fragments
import Ptx.Event.Memory

/-! Tagged, opaque 128-byte tensor-map objects. No tag is an actual CUDA byte;
the host encoder, state-space resolution and publication into the tensormap
proxy still need an external correspondence. Ordinary byte stores can overlap
these objects, so immutable-object rules quantify over the combined graph. -/
namespace Ptx.ISA.TensorMap
noncomputable section

def encode (view : Descriptor2D) : List Symbolic.Byte :=
  (List.range 128).map (fun index => .tensorMapPart view index)

def Stored (memory : Location → Symbolic.Byte) (base : Location) (view : Descriptor2D) : Prop :=
  ∀ offset, offset < 128 → memory (base.add offset) = .tensorMapPart view offset

@[simp] theorem encode_length (view : Descriptor2D) : (encode view).length = 128 := by simp [encode]

theorem encoded_byte (view : Descriptor2D) (base : Location) {offset : Nat} (ho : offset < 128) :
    Ptx.Event.payloadByte base (encode view) (base.add offset) = some (.tensorMapPart view offset) := by
  rw [Ptx.Event.payloadByte_offset]
  simp [encode,List.getElem?_map,List.getElem?_range ho]

theorem stored_unique {memory base left right} (hl : Stored memory base left) (hr : Stored memory base right) :
    left = right := by
  have hh := (hl 0 (by decide)).symm.trans (hr 0 (by decide))
  exact (Symbolic.Byte.tensorMapPart.inj hh).1

theorem integer_byte_not_tensor_map (value : Byte) (view : Descriptor2D) (offset : Nat) :
    Symbolic.Byte.bits value ≠ .tensorMapPart view offset := by intro h; cases h

end
end Ptx.ISA.TensorMap
