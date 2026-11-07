import Ptx.Kernels.ReleaseAcquireMessageDecomposition
import Ptx.Kernels.ReleaseAcquireMessageObservation
import Ptx.Ordered.Source

/-! Reconstruction for ALL well-formed completed candidates at the supported
launch. Candidate order, oracle values and finite polling counts are arbitrary.
The actual memory/initialization arguments remain separate from source shape. -/
namespace Ptx.Kernels.ReleaseAcquireMessage
open Ptx.ISA
noncomputable section

def dynamicConsumerEvents (retries flagValue payloadValue : Nat) : List Ordered.Kind :=
  List.replicate retries (acquireEvent 0) ++ [acquireEvent flagValue] ++ tailEvents payloadValue

theorem valid_source_thread {thread : ThreadId} (hi : thread.Valid launch.geometry) : thread = id 0 ∨ thread = id 1 := by
  rcases thread with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
  simp only [ThreadId.Valid,Dim3.Within,launch,block,Dim3.one] at hi
  have hz : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ ty = 0 ∧ tz = 0 := by omega
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := hz
  have hx : tx = 0 ∨ tx = 1 := by omega
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem arbitrary_producer_events {actualLaunch execution actualTrace}
    (hp : SourcePre actualLaunch) (hw : Ordered.WellFormed code actualLaunch execution)
    (hc : Ordered.Complete execution) (ht : actualTrace ∈ execution.traces) (hid : actualTrace.id = id 0) :
    actualTrace.count = 9 ∧ actualTrace.events = producerEvents := by
  have hr := (hw.2.2.1 actualTrace ht).2
  unfold Ordered.Produced at hr
  rw [hp.1,hp.2,hid] at hr
  exact completed_producer_events hr (hc actualTrace ht)

theorem arbitrary_consumer_events {actualLaunch execution actualTrace}
    (hp : SourcePre actualLaunch) (hw : Ordered.WellFormed code actualLaunch execution)
    (hc : Ordered.Complete execution) (ht : actualTrace ∈ execution.traces) (hid : actualTrace.id = id 1) :
    ∃ retries flagValue payloadValue, word flagValue ≠ 0 ∧
      actualTrace.events = dynamicConsumerEvents retries flagValue payloadValue := by
  have hr := (hw.2.2.1 actualTrace ht).2
  unfold Ordered.Produced at hr
  rw [hp.1,hp.2,hid] at hr
  exact completed_consumer_events hr (hc actualTrace ht)

theorem completed_member_events {actualLaunch execution actualTrace}
    (hp : SourcePre actualLaunch) (hw : Ordered.WellFormed code actualLaunch execution)
    (hc : Ordered.Complete execution) (ht : actualTrace ∈ execution.traces) :
    (actualTrace.id = id 0 ∧ actualTrace.events = producerEvents) ∨
    (actualTrace.id = id 1 ∧ ∃ retries flagValue payloadValue, word flagValue ≠ 0 ∧
      actualTrace.events = dynamicConsumerEvents retries flagValue payloadValue) := by
  have hi := (hw.2.2.1 actualTrace ht).1
  rw [hp.1] at hi
  rcases valid_source_thread hi with h0 | h1
  · exact Or.inl ⟨h0,(arbitrary_producer_events hp hw hc ht h0).2⟩
  · exact Or.inr ⟨h1,arbitrary_consumer_events hp hw hc ht h1⟩

theorem producer_is_present {actualLaunch execution} (hp : SourcePre actualLaunch)
    (hw : Ordered.WellFormed code actualLaunch execution) (hc : Ordered.Complete execution) :
    ∃ actualTrace ∈ execution.traces, actualTrace.id = id 0 ∧ actualTrace.events = producerEvents := by
  have hi : (id 0).Valid actualLaunch.geometry := by
    rw [hp.1]
    norm_num [id,launch,block,ThreadId.Valid,Dim3.Within,Dim3.zero,Dim3.one]
  obtain ⟨actualTrace,ht,hid⟩ := hw.2.2.2 (id 0) hi
  exact ⟨actualTrace,ht,hid,(arbitrary_producer_events hp hw hc ht hid).2⟩

theorem consumer_is_present {actualLaunch execution} (hp : SourcePre actualLaunch)
    (hw : Ordered.WellFormed code actualLaunch execution) (hc : Ordered.Complete execution) :
    ∃ actualTrace ∈ execution.traces, actualTrace.id = id 1 ∧
      ∃ retries flagValue payloadValue, word flagValue ≠ 0 ∧ actualTrace.events = dynamicConsumerEvents retries flagValue payloadValue := by
  have hi : (id 1).Valid actualLaunch.geometry := by
    rw [hp.1]
    norm_num [id,launch,block,ThreadId.Valid,Dim3.Within,Dim3.zero,Dim3.one]
  obtain ⟨actualTrace,ht,hid⟩ := hw.2.2.2 (id 1) hi
  exact ⟨actualTrace,ht,hid,arbitrary_consumer_events hp hw hc ht hid⟩

end
end Ptx.Kernels.ReleaseAcquireMessage
