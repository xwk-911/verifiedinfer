import Ptx.Kernels.FloatLiteralsUniversal

/-! Exact-real memory-model regressions for actual generated PTX. These are
Lean proofs, not GPU execution or IEEE rounding tests. -/
namespace Ptx.FloatMemoryTests
open Ptx.ISA Ptx.Event Ptx.FloatLiteralsMemory
noncomputable section

theorem generated_contract (dst : Nat) :
    Scalar.Triple Generated.float_literals.program (FloatLiteralsUniversal.Pre dst)
      (fun _ => domain dst) (fun _ output => observedValue dst output = some 9) :=
  FloatLiteralsUniversal.correct dst

theorem generated_nonvacuous (dst : Nat) :
    Scalar.Nonvacuous Generated.float_literals.program (FloatLiteralsUniversal.Pre dst)
      (fun _ => domain dst) := FloatLiteralsUniversal.nonvacuous dst

def initial : Scalar.ByteMap := fun _ => .bits (byte 165)

theorem instance_wellFormed :
    Scalar.WellFormed Generated.float_literals.program (launch 64 initial) (graph 64 9) :=
  wellFormed 64 9 initial (by decide)

theorem instance_output : observedValue 64 (observation 64 initial).output = some 9 :=
  output_correct (consistent 64 initial) (observed 64 initial) rfl

theorem wrong_shared_answer (rf : ReadsFrom) (co : Coherence) :
    ¬ GenericMemoryConditions (graph 64 17) initial rf co := wrong_answer_rejected 64 initial rf co

theorem missing_thread :
    ¬ Scalar.WellFormed Generated.float_literals.program (launch 64 initial) ⟨[]⟩ := by
  intro hw
  obtain ⟨t,ht,_⟩ := hw.2.2.2 thread
    (by simp [launch,thread,ThreadId.Valid,Dim3.Within,Dim3.zero,Dim3.one])
  simp at ht

theorem duplicate_thread :
    ¬ Scalar.WellFormed Generated.float_literals.program (launch 64 initial)
      ⟨[trace 64 9,trace 64 9]⟩ := by
  intro hw
  simpa using hw.2.1

theorem forged_instruction_count :
    ¬ Scalar.Produced Generated.float_literals.program [("dst",64)] {(trace 64 9) with count := 7} := by
  intro hp
  obtain ⟨_,hcount,_,_⟩ := FloatLiteralsUniversal.trace_shape rfl (by decide) hp rfl
  norm_num [trace] at hcount

theorem wrong_reply_type :
    ¬ Scalar.Produced Generated.float_literals.program [("dst",64)]
      {(trace 64 9) with oracle := fun _ => .integer 0} := by
  intro hp
  obtain ⟨floats,hr⟩ := hp
  obtain ⟨answer,hq⟩ := FloatLiteralsUniversal.complete_oracle_reply rfl (by decide) hr rfl
  cases hq

end
end Ptx.FloatMemoryTests
