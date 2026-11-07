import Ptx.Kernels.ReleaseAcquireMessageUniversalSource
import Ptx.Ordered.ReadRules

/-! Arbitrary completed-source reconstruction, real retry instances, typed
oracle failures and initialization-derived flag observation. The universal
memory/observer kernel VC remains a separate obligation. -/
namespace Ptx.OrderedLoopTests
open Ptx.ISA Ptx.Kernels.ReleaseAcquireMessage
noncomputable section

theorem all_completed_consumers_have_finite_poll_shape {answers : Ordered.Oracle} {count final events}
    (hr : Ordered.run (context 1) answers code count {} = .ok (final,events))
    (hd : final.core.thread.status = .done) :
    ∃ retries flagValue payloadValue, word flagValue ≠ 0 ∧ events = dynamicConsumerEvents retries flagValue payloadValue :=
  completed_consumer_events hr hd

theorem all_completed_launch_members_have_source_shapes {actualLaunch execution actualTrace}
    (hp : SourcePre actualLaunch) (hw : Ordered.WellFormed code actualLaunch execution)
    (hc : Ordered.Complete execution) (ht : actualTrace ∈ execution.traces) :
    (actualTrace.id = Kernels.ReleaseAcquireMessage.id 0 ∧ actualTrace.events = producerEvents) ∨
    (actualTrace.id = Kernels.ReleaseAcquireMessage.id 1 ∧ ∃ retries flagValue payloadValue, word flagValue ≠ 0 ∧
      actualTrace.events = dynamicConsumerEvents retries flagValue payloadValue) := completed_member_events hp hw hc ht

theorem real_retry_has_one_zero_poll_then_nonzero_and_payload :
    retryTrace.events = dynamicConsumerEvents 1 1 42 := rfl

theorem retry_shape_is_derived_from_actual_run :
    ∃ retries flagValue payloadValue, word flagValue ≠ 0 ∧ retryTrace.events = dynamicConsumerEvents retries flagValue payloadValue :=
  completed_consumer_events polling_retry_is_an_actual_source_run rfl

theorem arbitrary_running_poll_cannot_finish_in_two_steps {state : Ordered.State} {answers count final events}
    (hp : AtPoll state) (hn : count < 3)
    (hr : Ordered.run (context 1) answers code count state = .ok (final,events)) : final.core.thread.status ≠ .done := by
  rw [poll_short_running hp hn hr]
  intro h; cases h

theorem successful_poll_requires_an_integer_reply {state : Ordered.State} {answers next events}
    (hp : AtPoll state) (hr : Ordered.step (context 1) answers code state = .ok (next,events)) :
    ∃ value, answers state.core.queries = .integer value := poll_reply hp hr

theorem zero_initial_flag_is_represented : Scalar.RepresentsU32 launch.initial flag 0 := by
  intro offset hoffset
  have hcases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> rfl

theorem initialized_nonzero_flag_derives_observation :
    ∃ offset, offset < 4 ∧ rf flagRead (flag.add offset) = .write flagWrite := by
  have he : candidate.view.eventAt flagRead = some (.read flag (Scalar.u32Bytes 1)) := rfl
  apply Ordered.nonzero_u32_read_observes_writer (actual_memory_consistent launch.initial) he
  · intro offset hoffset
    apply Ordered.unique_writer_strong_read_eligible (no_mixed_size_races rf) _
      (Ordered.morally_strong_symm flag_endpoints_are_mutually_strong)
    intro other value hother
    have hown : candidate.view.writeByte flagWrite (flag.add offset) = some (Scalar.u32Byte 1 offset) := by
      have hw : candidate.view.eventAt flagWrite = some (.write flag (Scalar.u32Bytes 1)) := rfl
      simpa only [Ptx.Event.Candidate.writeByte,hw,Option.bind_some,Ptx.Event.Kind.writeByte]
        using Scalar.u32_payload_byte flag 1 offset hoffset
    exact unique_byte_writer hother hown
  · exact zero_initial_flag_is_represented
  · decide
  · decide
  · intro offset hoffset other value hother
    have hown : candidate.view.writeByte flagWrite (flag.add offset) = some (Scalar.u32Byte 1 offset) := by
      have hw : candidate.view.eventAt flagWrite = some (.write flag (Scalar.u32Bytes 1)) := rfl
      simpa only [Ptx.Event.Candidate.writeByte,hw,Option.bind_some,Ptx.Event.Kind.writeByte]
        using Scalar.u32_payload_byte flag 1 offset hoffset
    exact unique_byte_writer hother hown

end
end Ptx.OrderedLoopTests
