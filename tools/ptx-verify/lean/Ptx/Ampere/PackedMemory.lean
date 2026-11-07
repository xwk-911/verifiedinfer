import Ptx.Ampere.PackedF16
import Ptx.Scalar.Memory
import Mathlib.Tactic.FinCases

/-! Bytewise symbolic f16 half extraction. No integer reinterpretation or IEEE
encoding is introduced by these logical packed-register rules. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

def PackedF16.half (p : PackedF16) (i : Fin 2) : ℝ := if i.val = 0 then p.low else p.high

theorem PackedF16.half_byte (p : PackedF16) (base : Location) (half offset : Fin 2) :
    Ptx.Event.payloadByte base p.encode (base.add (2*half.val+offset.val)) =
      some (.realPart .f16 (p.half half) offset.val) := by
  rw [Ptx.Event.payloadByte_offset]
  fin_cases half <;> fin_cases offset <;> rfl

theorem PackedF16.ext_half {a b : PackedF16} (h : ∀ half, a.half half = b.half half) : a = b := by
  have hl := h 0
  have hh := h 1
  cases a; cases b
  simp only [half,Fin.val_zero,Fin.val_one,ite_true] at hl hh
  simp_all

end
end Ptx.Ampere
