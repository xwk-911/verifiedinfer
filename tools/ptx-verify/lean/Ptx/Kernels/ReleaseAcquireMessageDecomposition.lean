import Ptx.Kernels.ReleaseAcquireMessageLoop
import Ptx.Kernels.ReleaseAcquireMessageGraph

/-! Exact events of arbitrary completed source runs. The consumer may have any
finite number of zero-flag polls before its nonzero final acquire. No canonical
oracle, fixed step count or memory consistency is substituted into this proof. -/
namespace Ptx.Kernels.ReleaseAcquireMessage
open Ptx.ISA
noncomputable section

theorem zero_acquire_event {value : Nat} (hz : word value = 0) : acquireEvent value = acquireEvent 0 := by
  unfold acquireEvent
  rw [hz]
  rfl

theorem poll_chunks_events {answers : Ordered.Oracle} {state leaving : Ordered.State} {events}
    (hc : Ordered.LoopChunks (context 1) answers code 3 AtPoll AtTail state events leaving) (hp : AtPoll state) :
    ∃ retries value, word value ≠ 0 ∧ events = List.replicate retries (acquireEvent 0) ++ [acquireEvent value] := by
  revert hp
  induction hc with
  | stop hexit =>
    intro hp
    have h := hp.2.1.symm.trans hexit.2.1
    omega
  | next hkeep hrun htail ih =>
    intro _
    obtain ⟨value,_,rfl,rfl⟩ := poll_chunk_shape hkeep hrun
    by_cases hz : word value = 0
    · have hp : AtPoll (branched _ value) := ⟨branched_pointers hkeep.1 value,
        by simp [branched,Scalar.finishInteger,hz],
        by simpa [branched,compared,polled,Scalar.finishInteger,assign,advance] using hkeep.2.2⟩
      obtain ⟨retries,lastValue,hlast,he⟩ := ih hp
      refine ⟨retries+1,lastValue,hlast,?_⟩
      rw [he,zero_acquire_event hz]
      simp only [List.replicate_succ,List.cons_append,List.nil_append]
    · have hp : AtTail (branched _ value) := ⟨branched_pointers hkeep.1 value,
        by simp [branched,Scalar.finishInteger,hz],
        by simpa [branched,compared,polled,Scalar.finishInteger,assign,advance] using hkeep.2.2⟩
      cases htail with
      | stop => exact ⟨0,value,hz,by simp⟩
      | next hm _ _ =>
        have h := hm.2.1.symm.trans hp.2.1
        omega

def consumerPrefix : Ordered.State := (result 1 6).1

theorem consumer_prefix (answers : Ordered.Oracle) :
    Ordered.run (context 1) answers code 6 {} = .ok (consumerPrefix,[]) := rfl

theorem consumer_prefix_at_poll : AtPoll consumerPrefix := ⟨⟨rfl,rfl,rfl⟩,rfl,rfl⟩

theorem completed_consumer_events {answers : Ordered.Oracle} {count final events}
    (hr : Ordered.run (context 1) answers code count {} = .ok (final,events))
    (hd : final.core.thread.status = .done) :
    ∃ retries flagValue payloadValue, word flagValue ≠ 0 ∧
      events = List.replicate retries (acquireEvent 0) ++ [acquireEvent flagValue] ++ tailEvents payloadValue := by
  have hprefix := consumer_prefix answers
  have hcount := Ordered.completed_after_running_prefix hr hd hprefix consumer_prefix_at_poll.2.2
  obtain ⟨remaining,rest,_,hrest,hevents⟩ := Ordered.successful_suffix (Nat.le_of_lt hcount) hprefix hr
  obtain ⟨leaving,first,tail,hchunks,hexit,htail,hfinal⟩ :=
    Ordered.completed_loop_decomposition (by decide : 0 < 3)
      (fun _ hp _ hc _ _ hr => poll_short_running hp hc hr)
      (fun _ hp _ _ hr => poll_chunk_closed hp hr)
      (fun _ hp _ hc _ _ hr => tail_short_running hp hc hr)
      (fun _ hp _ _ hr => tail_chunk_finishes hp hr)
      consumer_prefix_at_poll hrest hd
  obtain ⟨retries,flagValue,hflag,hfirst⟩ := poll_chunks_events hchunks consumer_prefix_at_poll
  obtain ⟨payloadValue,_,_,rfl⟩ := tail_chunk_shape hexit htail
  exact ⟨retries,flagValue,payloadValue,hflag,by simpa only [List.nil_append,hfirst] using hevents.trans hfinal⟩

theorem producer_run_for_any_oracle (answers : Ordered.Oracle) :
    Ordered.run (context 0) answers code 9 {} = .ok ((trace 0 9).final,producerEvents) := rfl

theorem completed_producer_events {answers : Ordered.Oracle} {count final events}
    (hr : Ordered.run (context 0) answers code count {} = .ok (final,events))
    (hd : final.core.thread.status = .done) : count = 9 ∧ events = producerEvents := by
  have hu := Ordered.complete_run_unique hr hd (producer_run_for_any_oracle answers)
    (show (trace 0 9).final.core.thread.status = .done from rfl)
  exact ⟨hu.1,hu.2.2⟩

end
end Ptx.Kernels.ReleaseAcquireMessage
