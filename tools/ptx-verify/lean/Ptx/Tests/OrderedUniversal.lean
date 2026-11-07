import Ptx.Kernels.ReleaseAcquireMessageUniversal
import Ptx.Tests.OrderedLoop

/-! The universal contract is separate from existence. A typed, complete source
execution with a wrong payload is rejected by memory consistency for EVERY
reads-from/coherence choice, not only by a preselected witness. -/
namespace Ptx.OrderedUniversalTests
open Ptx.ISA Ptx.Kernels.ReleaseAcquireMessage
noncomputable section

theorem concrete_pre : Pre launch := ⟨⟨rfl,rfl⟩,OrderedLoopTests.zero_initial_flag_is_represented⟩

theorem concrete_complete_legal_execution_exists :
    ∃ execution sources co observation, Ordered.WellFormed code launch execution ∧ Ordered.Complete execution ∧
      Ordered.MemoryConditions execution launch.initial sources co ∧
      Ordered.ObserverConditions execution launch.initial sources co observation ∧ observation.domain = domain :=
  initialized_nonvacuous launch concrete_pre

def wrongOracle : Ordered.Oracle := fun query => .integer (if query = 0 then 1 else 99)
def wrongResult : Ordered.State × List Ordered.Kind :=
  (Ordered.run (context 1) wrongOracle code 12 {}).toOption.getD ({},[])
def wrongTrace : Ordered.ThreadTrace := ⟨Kernels.ReleaseAcquireMessage.id 1,wrongOracle,12,wrongResult.1,wrongResult.2⟩
-- Deliberately reverse source trace order, keeping the original PTX.
def wrongCandidate : Ordered.Candidate := ⟨[wrongTrace,trace 0 9]⟩

theorem wrong_reply_is_still_a_typed_complete_source_run :
    Ordered.Produced code bindings block wrongTrace ∧ wrongTrace.final.core.thread.status = .done := ⟨rfl,rfl⟩

theorem wrong_candidate_complete : Ordered.Complete wrongCandidate := by
  intro actual ht
  simp only [wrongCandidate,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl

theorem wrong_candidate_source_valid : Ordered.WellFormed code launch wrongCandidate := by
  refine ⟨source_candidate_is_well_formed.1,?_,?_,?_⟩
  · change ([Kernels.ReleaseAcquireMessage.id 1,Kernels.ReleaseAcquireMessage.id 0].Nodup)
    decide
  · intro actual ht
    simp only [wrongCandidate,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨by norm_num [wrongTrace,Kernels.ReleaseAcquireMessage.id,launch,block,ThreadId.Valid,Dim3.Within,Dim3.zero,Dim3.one],rfl⟩
    · exact ⟨by norm_num [trace,Kernels.ReleaseAcquireMessage.id,launch,block,ThreadId.Valid,Dim3.Within,Dim3.zero,Dim3.one],producer_source_run⟩
  · intro thread hi
    rcases valid_source_thread hi with h0 | h1
    · exact ⟨trace 0 9,by simp [wrongCandidate],h0.symm⟩
    · exact ⟨wrongTrace,by simp [wrongCandidate],h1.symm⟩

theorem wrong_candidate_shape : CompletedShape wrongCandidate 0 1 99 := by
  refine ⟨by decide,?_,?_,?_⟩
  · intro serial
    rw [Ordered.kindAt_of_member wrong_candidate_source_valid.2.1
      (show trace 0 9 ∈ wrongCandidate.traces by simp [wrongCandidate]) (by rfl)]
    rfl
  · intro serial
    rw [Ordered.kindAt_of_member wrong_candidate_source_valid.2.1
      (show wrongTrace ∈ wrongCandidate.traces by simp [wrongCandidate]) (by rfl)]
    rfl
  · obtain ⟨_,_,_,hs⟩ := completed_shape concrete_pre.1 wrong_candidate_source_valid wrong_candidate_complete
    exact hs.threads

theorem wrong_completed_source_is_rejected_for_all_memory_choices (sources : Ptx.Event.ReadsFrom) (co : Ptx.Event.Coherence) :
    ¬Ordered.MemoryConditions wrongCandidate launch.initial sources co := by
  intro hm
  have he := wrong_candidate_shape.payload_value hm concrete_pre.2
  norm_num [word,wrap] at he

end
end Ptx.OrderedUniversalTests
