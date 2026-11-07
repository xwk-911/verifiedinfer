import Std

/-! Little-endian u32 memory payloads. These are actual bytes; real-valued floats
use the separate symbolic fragments in Fragments.lean and cannot be cast here. -/
namespace Ptx.ISA

abbrev Byte := Fin 256

def byte (n : Nat) : Byte := ⟨n % 256, Nat.mod_lt _ (by decide)⟩

def encodeU32 (n : Nat) : List Byte :=
  [byte n, byte (n / 256), byte (n / 65536), byte (n / 16777216)]

def decodeLE : List Byte → Nat
  | [] => 0
  | b :: bs => b.val + 256 * decodeLE bs

@[simp] theorem encodeU32_length (n : Nat) : (encodeU32 n).length = 4 := rfl

theorem decode_encodeU32 (n : Nat) : decodeLE (encodeU32 n) = n % 2^32 := by
  simp only [encodeU32, decodeLE, byte]
  omega

end Ptx.ISA
