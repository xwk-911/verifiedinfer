import Ptx.Kernels.ShufflePairUniversal

/-! Arbitrary-oracle and reordered-trace witnesses, exact completion counts,
source coverage failures, and real ordinary-memory/observer witnesses. -/
namespace Ptx.ShuffleUniversalTests
open Ptx.ISA Ptx.Shuffle
open Ptx.Kernels.ShufflePair
noncomputable section

def changedAnswers (which : Lane2) : Shuffle.Oracle :=
  ⟨fun query => .integer (999+query),fun query => if query = 0 then (1-which.val,true) else (4294967303+query,false)⟩
def changedTrace (which : Lane2) : Shuffle.ThreadTrace :=
  {trace which (1-which.val) true with oracle := changedAnswers which}
def reordered : Shuffle.Candidate := ⟨[changedTrace 1,changedTrace 0]⟩

theorem changed_oracles_produce_the_same_register_trace (which : Lane2) :
    Produced Generated.shuffle_pair.program [] block (changedTrace which) := arbitrary_oracle_source_run which (changedAnswers which) []

theorem reordered_source_well_formed (initial : Location → Symbolic.Byte) :
    WellFormed Generated.shuffle_pair.program (launch initial) reordered := by
  refine ⟨by simp [launch,block,Geometry.Valid,Dim3.Positive,Dim3.one],by simp [reordered,changedTrace,trace,Ptx.Kernels.ShufflePair.id],?_,?_⟩
  · intro actual ht
    simp only [reordered,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    all_goals refine ⟨?_,changed_oracles_produce_the_same_register_trace _⟩
    all_goals simp [changedTrace,trace,launch,Ptx.Kernels.ShufflePair.id,ThreadId.Valid,Dim3.Within,Dim3.one,Dim3.zero,block]
  · intro thread ht
    obtain ⟨which,rfl⟩ := valid_thread_is_lane ht
    fin_cases which
    · exact ⟨changedTrace 0,by simp [reordered],rfl⟩
    · exact ⟨changedTrace 1,by simp [reordered],rfl⟩

theorem reordered_complete : Complete reordered := by
  intro actual ht
  simp only [reordered,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl

theorem reordered_events_are_equal (actual : Ptx.Event.EventId) :
    reordered.eventAt actual = (candidate 1 0 true true).eventAt actual := by
  by_cases h0 : Ptx.Kernels.ShufflePair.id 0 = actual.thread
  · by_cases h1 : Ptx.Kernels.ShufflePair.id 1 = actual.thread
    · have hi := h0.trans h1.symm
      cases hi
    · simp [Shuffle.Candidate.eventAt,reordered,candidate,changedTrace,trace,h0,h1]
  · by_cases h1 : Ptx.Kernels.ShufflePair.id 1 = actual.thread
    all_goals simp [Shuffle.Candidate.eventAt,reordered,candidate,changedTrace,trace,h0,h1]

theorem reordered_agreement : Agreement block reordered := by
  have ha := (pair_agreement_iff 1 0 true true).2 (by decide)
  intro origin result he _ peer input hp hs
  have he' : (candidate 1 0 true true).shuffleAt origin = some result := by
    simpa only [Shuffle.Candidate.shuffleAt,reordered_events_are_equal] using he
  have hp' : (candidate 1 0 true true).shuffleAt peer = some input := by
    simpa only [Shuffle.Candidate.shuffleAt,reordered_events_are_equal] using hp
  exact ha origin result he' ((pair_defined 1 0 true true) origin result he').1 peer input hp' hs

theorem reordered_defined_and_control_admitted (initial : Location → Symbolic.Byte) :
    Defined block reordered ∧ ControlAdmitted block reordered := by
  have hp : Pre (launch initial) := ⟨rfl,rfl⟩
  exact ⟨actual_defined hp (reordered_source_well_formed initial) reordered_complete,
    actual_control_admitted hp (reordered_source_well_formed initial) reordered_complete⟩

theorem reordered_registers_correct (initial : Location → Symbolic.Byte) :
    ∀ actual ∈ reordered.traces, RegisterPost actual.id actual.final :=
  all_completed_registers_correct (show Pre (launch initial) from ⟨rfl,rfl⟩)
    (reordered_source_well_formed initial) reordered_complete reordered_agreement

theorem changed_memory_and_future_answers_are_unused :
    (changedAnswers 0).memory 0 = .integer 999 ∧ (changedAnswers 0).shuffle 1 = (4294967304,false) ∧
    (changedTrace 0).final.queries = 1 := ⟨rfl,rfl,rfl⟩

theorem completion_cannot_be_padded :
    Shuffle.run {id := Ptx.Kernels.ShufflePair.id 0,block := block} (changedAnswers 0) Generated.shuffle_pair.program 4 {} =
      .error (.integer .blocked) := by
  rw [show 4 = 3+1 from rfl,Shuffle.run_add,arbitrary_oracle_source_run 0 (changedAnswers 0) []]
  simp [Except.bind,Except.map,Shuffle.run_done_suffix (show (finalState 0 _ _).base.core.thread.status = .done from rfl) 0]

theorem padded_trace_is_not_source_produced :
    ¬Produced Generated.shuffle_pair.program [] block {changedTrace 0 with count := 4} := by
  intro hp
  have hn := (completed_trace_shape 0 (by rfl) hp (by rfl)).1
  norm_num [changedTrace] at hn

theorem missing_participant_is_not_well_formed (initial : Location → Symbolic.Byte) :
    ¬WellFormed Generated.shuffle_pair.program (launch initial) ⟨[changedTrace 0]⟩ := by
  intro hw
  have hv : (Ptx.Kernels.ShufflePair.id 1).Valid (launch initial).geometry := by
    simp [Ptx.Kernels.ShufflePair.id,launch,ThreadId.Valid,Dim3.Within,Dim3.one,Dim3.zero,block]
  obtain ⟨actual,ht,hi⟩ := hw.2.2.2 _ hv
  simp only [List.mem_singleton] at ht
  subst actual
  cases hi

theorem arbitrary_global_frame_is_preserved (domain : List Location) :
    Shuffle.Triple Generated.shuffle_pair.program Pre (fun _ => domain)
      (fun launch output => ∀ loc ∈ domain, output loc = launch.initial loc) := all_completed_memory_frame domain

theorem a_nonempty_observation_has_a_complete_witness :
    Shuffle.Nonvacuous Generated.shuffle_pair.program Pre (fun _ => [⟨.global,8⟩,⟨.global,9⟩]) :=
  source_nonvacuous _ (by intro loc hl; simp only [List.mem_cons,List.not_mem_nil,or_false] at hl; rcases hl with rfl | rfl <;> rfl)

theorem source_definedness_is_not_an_extra_precondition : Shuffle.Safe Generated.shuffle_pair.program Pre := source_safe

end
end Ptx.ShuffleUniversalTests
