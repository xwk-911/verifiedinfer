import Ptx.ISA.Bytes
import Ptx.ISA.TensorMapView
import Mathlib.Basic.Real.Basic

/-! Symbolic real-valued floating storage, following the paper's abstraction.
These fragments are NOT IEEE bytes. Neither integer decoding nor bitwise float
reinterpretation is supplied. Formats determine storage width, not rounding.
-/
namespace Ptx.ISA.Symbolic
noncomputable section

inductive Format | f16 | f32 | f64 deriving Repr, DecidableEq
def Format.bytes : Format → Nat
  | .f16 => 2
  | .f32 => 4
  | .f64 => 8

inductive Byte where
  | bits (value : Ptx.ISA.Byte)
  | realPart (format : Format) (value : ℝ) (index : Nat)
  | tensorMapPart (view : TensorMap.Descriptor2D) (index : Nat)

def encode (format : Format) (value : ℝ) : List Byte :=
  (List.range format.bytes).map (fun index => .realPart format value index)

def decode (format : Format) (bytes : List Byte) : Option ℝ := by
  classical
  exact match bytes.head? with
  | some (.realPart actual value index) =>
      if index = 0 ∧ actual = format ∧ bytes = encode format value then some value else none
  | _ => none

@[simp] theorem encode_length (format : Format) (value : ℝ) : (encode format value).length = format.bytes := by
  simp [encode]

@[simp] theorem decode_encode (format : Format) (value : ℝ) : decode format (encode format value) = some value := by
  cases format <;> simp [decode,encode,Format.bytes,List.range_succ]

theorem decode_eq_some_iff {format bytes value} : decode format bytes = some value ↔ bytes = encode format value := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · split at h
      · rename_i actual observed index hh hc
        have hv : observed = value := Option.some.inj h
        simpa only [hv] using hc.2.2
      · cases h
    · cases h
  · rintro rfl
    exact decode_encode _ _

theorem encode_injective (format : Format) : Function.Injective (encode format) := by
  intro a b h
  have hv := congrArg (decode format) h
  simpa only [decode_encode,Option.some.injEq] using hv

theorem decode_length_mismatch {format bytes} (h : bytes.length ≠ format.bytes) : decode format bytes = none := by
  cases hd : decode format bytes with
  | none => rfl
  | some value =>
    have he := decode_eq_some_iff.mp hd
    exact (h (by rw [he,encode_length])).elim

theorem integer_bytes_not_floats (format : Format) (bytes : List Ptx.ISA.Byte) :
    decode format (bytes.map Byte.bits) = none := by
  cases bytes <;> simp [decode]

theorem torn_f32_rejected (x y : ℝ) (h : x ≠ y) :
    decode .f32 [.realPart .f32 x 0,.realPart .f32 x 1,.realPart .f32 y 2,.realPart .f32 y 3] = none := by
  simp [decode,encode,Format.bytes,List.range_succ,Ne.symm h]

theorem reordered_f32_rejected (x : ℝ) :
    decode .f32 [.realPart .f32 x 1,.realPart .f32 x 0,.realPart .f32 x 2,.realPart .f32 x 3] = none := by
  simp [decode]

end
end Ptx.ISA.Symbolic
