import Ptx.Hopper.WgmmaDescriptor
import Ptx.ISA.Shift

/-! Runtime shared-address encoding for the fixed packed profile. The base
comes from the actual shared symbol, rather than a presumed symbol placement.
The bounds/alignment premises are layout obligations, not assumed GPU addresses.
-/
namespace Ptx.Hopper.Wgmma
set_option maxRecDepth 50000
open Ptx.ISA

def encodeShared (base : Nat) : Nat := base/16+68720001024
theorem runtime_descriptor_profile {base : Nat} (hb : base < 262144) (ha : base%16 = 0) :
    MatrixDescriptor.Packed (encodeShared base) ∧ (MatrixDescriptor.decode (encodeShared base)).base = base := by
  let descriptor : MatrixDescriptor := ⟨⟨base/16,by omega⟩,8,16⟩
  have he : encodeShared base = descriptor.encode := (Nat.add_assoc (base/16) (65536*8) (4294967296*16)).symm
  rw [he]
  refine ⟨⟨descriptor_encoded_canonical descriptor,?_⟩,?_⟩
  · rw [descriptor_decode_encode]
    exact ⟨rfl,rfl⟩
  · rw [descriptor_decode_encode]
    dsimp [descriptor,MatrixDescriptor.base]
    omega
theorem runtime_shift_extracts_start {base : Nat} (hb : base < 262144) (thread : Thread) (tid : Nat) :
    localStep [] tid thread (.bin .shr 64 64 "descriptor" (.imm base) (.imm 4)) =
      .ok (assign thread "descriptor" (base/16)) := by
  rw [unsigned_shift_local 64 base 4 (by simp)]
  have hw : base < 2^64 := by omega
  have hd : base/16 < 2^64 := by omega
  change (Except.ok (assign thread "descriptor" (wrap 64 (wrap 64 base/16))) : Except Ptx.Fault Thread) = _
  simp only [wrap,Nat.mod_eq_of_lt hw,Nat.mod_eq_of_lt hd]

end Ptx.Hopper.Wgmma
