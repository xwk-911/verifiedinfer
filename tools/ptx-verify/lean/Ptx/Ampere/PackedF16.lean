import Ptx.ISA.Fragments

/-! A typed logical f16 pair and its symbolic storage. Packing preserves two
real-valued half fragments; it does not expose IEEE bits or allow integer
reinterpretation. Source register-bank integration is a separate obligation.
-/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

structure PackedF16 where
  low : ℝ
  high : ℝ

def PackedF16.encode (p : PackedF16) : List Symbolic.Byte :=
  Symbolic.encode .f16 p.low ++ Symbolic.encode .f16 p.high
def PackedF16.decode (bytes : List Symbolic.Byte) : Option PackedF16 := do
  if bytes.length ≠ 4 then none else do
    let low ← Symbolic.decode .f16 (bytes.take 2)
    let high ← Symbolic.decode .f16 (bytes.drop 2)
    some ⟨low,high⟩

@[simp] theorem PackedF16.encode_size (p : PackedF16) : p.encode.length = 4 := by
  simp [encode,Symbolic.Format.bytes]
@[simp] theorem PackedF16.decode_encode (p : PackedF16) : decode p.encode = some p := by
  have ht : p.encode.take 2 = Symbolic.encode .f16 p.low := by
    simp [encode,Symbolic.encode,Symbolic.Format.bytes,List.range_succ]
  have hd : p.encode.drop 2 = Symbolic.encode .f16 p.high := by
    simp [encode,Symbolic.encode,Symbolic.Format.bytes,List.range_succ]
  simp [decode,ht,hd]

theorem PackedF16.decode_eq_some_iff {bytes p} : decode bytes = some p ↔ bytes = encode p := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · cases h
    · cases hl : Symbolic.decode .f16 (bytes.take 2) with
      | none => simp [hl] at h
      | some low =>
        cases hh : Symbolic.decode .f16 (bytes.drop 2) with
        | none => simp [hl,hh] at h
        | some high =>
          have he : PackedF16.mk low high = p := by simpa [hl,hh] using h
          subst p
          have ht := Symbolic.decode_eq_some_iff.mp hl
          have hd := Symbolic.decode_eq_some_iff.mp hh
          exact (List.take_append_drop 2 bytes).symm.trans (congrArg₂ List.append ht hd)
  · rintro rfl
    exact decode_encode p

theorem PackedF16.encode_injective : Function.Injective encode := by
  intro a b h
  have he := congrArg decode h
  simpa only [decode_encode,Option.some.injEq] using he
theorem PackedF16.integer_storage_rejected (bytes : List Ptx.ISA.Byte) :
    decode (bytes.map Symbolic.Byte.bits) = none := by
  simp [decode,← List.map_take,Symbolic.integer_bytes_not_floats]

end
end Ptx.Ampere
