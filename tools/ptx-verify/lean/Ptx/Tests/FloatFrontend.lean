import Ptx.Kernels.FloatFmaTrace
import Ptx.Kernels.FloatLiteralsTrace

/-! Tests of the actual generated float PTX, with local trace/provenance evidence
clearly separated from the memory/observer contract in Tests.FloatMemory.
-/
namespace Ptx.FloatFrontendTests
open Ptx.ISA Ptx.Scalar
noncomputable section

theorem fma_generated_types : Scalar.ProgramTyped Generated.float_fma.registerDeclarations
    Generated.float_fma.parameters Generated.float_fma.program := Generated.float_fma.checked.valid
theorem literals_generated_types : Scalar.ProgramTyped Generated.float_literals.registerDeclarations
    Generated.float_literals.parameters Generated.float_literals.program := Generated.float_literals.checked.valid

def lastWrittenValue (events : List Scalar.Kind) : Option ℝ := match events.getLast? with
  | some (.write _ bytes) => Symbolic.decode .f32 bytes
  | _ => none

theorem translated_fma_local_witness (ctx : Event.Context) (src dst : Nat) (a b c : ℝ)
    (hp : FloatFmaTrace.Params src dst ctx.params) (hs : src+8 < 2^64) (hd : dst < 2^64) :
    ∃ final events, Scalar.run ctx (FloatFmaTrace.oracle a b c) Generated.float_fma.program 8 {} = .ok (final,events) ∧
      final.core.thread.status = .done ∧ lastWrittenValue events = some (a*b+c) := by
  refine ⟨FloatFmaTrace.finalState src dst a b c,FloatFmaTrace.events src dst a b c,
    FloatFmaTrace.translated_trace ctx src dst a b c hp hs hd,rfl,?_⟩
  simp [lastWrittenValue,FloatFmaTrace.events]

/-- A locally complete translated execution can still use the WRONG shared-read
answer. A later global memory proof must rule it out; the frontend cannot assume 9. -/
theorem wrong_answer_is_locally_produced (ctx : Event.Context) (dst : Nat)
    (hp : lookup "dst" ctx.params = some dst) (hd : dst < 2^64) :
    ∃ final events, Scalar.run ctx (fun _ => .real .f32 17) Generated.float_literals.program 8 {} = .ok (final,events) ∧
      final.core.thread.status = .done ∧ lastWrittenValue events = some 17 ∧
      events[0]? = some (.write ⟨.shared ctx.id.cta,0⟩ (Symbolic.encode .f32 9)) := by
  refine ⟨FloatLiteralsTrace.finalState dst 17,FloatLiteralsTrace.events ctx.id dst 17,
    FloatLiteralsTrace.translated_trace ctx dst 17 hp hd,rfl,?_,rfl⟩
  simp [lastWrittenValue,FloatLiteralsTrace.events]

theorem infinity_literal_cannot_be_certified : ¬ ∃ literal : F32Literal, literal.bits = 2139095040 := by
  rintro ⟨literal,he⟩
  have hf := literal.finite
  rw [he] at hf
  norm_num at hf

theorem nan_literal_cannot_be_certified : ¬ ∃ literal : F32Literal, literal.bits = 2143289345 := by
  rintro ⟨literal,he⟩
  have hf := literal.finite
  rw [he] at hf
  norm_num at hf

end
end Ptx.FloatFrontendTests
