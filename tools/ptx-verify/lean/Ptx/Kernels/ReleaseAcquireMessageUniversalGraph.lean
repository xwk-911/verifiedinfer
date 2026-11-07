import Ptx.Kernels.ReleaseAcquireMessageUniversalSource

/-! Exact event lookup for arbitrary completed source candidates. The number of
zero polls, oracle answers and trace order are unrestricted. Source shape is
derived from execution; it is not a memory-admission or correctness premise. -/
namespace Ptx.Kernels.ReleaseAcquireMessage
open Ptx.ISA
noncomputable section

def finalFlagRead (retries : Nat) : Ptx.Event.EventId := ⟨id 1,retries⟩
def finalPayloadRead (retries : Nat) : Ptx.Event.EventId := ⟨id 1,retries+1⟩
def finalOutputWrite (retries : Nat) : Ptx.Event.EventId := ⟨id 1,retries+2⟩

structure CompletedShape (execution : Ordered.Candidate) (retries flagValue payloadValue : Nat) : Prop where
  nonzero : word flagValue ≠ 0
  producer : ∀ serial, execution.kindAt ⟨id 0,serial⟩ = producerEvents[serial]?
  consumer : ∀ serial, execution.kindAt ⟨id 1,serial⟩ = (dynamicConsumerEvents retries flagValue payloadValue)[serial]?
  threads : ∀ event kind, execution.kindAt event = some kind → event.thread = id 0 ∨ event.thread = id 1

theorem completed_shape {actualLaunch execution} (hp : SourcePre actualLaunch)
    (hw : Ordered.WellFormed code actualLaunch execution) (hc : Ordered.Complete execution) :
    ∃ retries flagValue payloadValue, CompletedShape execution retries flagValue payloadValue := by
  obtain ⟨producer,htp,hidp,hep⟩ := producer_is_present hp hw hc
  obtain ⟨consumer,htc,hidc,retries,flagValue,payloadValue,hn,hec⟩ := consumer_is_present hp hw hc
  refine ⟨retries,flagValue,payloadValue,hn,?_,?_,?_⟩
  · intro serial
    rw [Ordered.kindAt_of_member hw.2.1 htp (by exact hidp.symm),hep]
  · intro serial
    rw [Ordered.kindAt_of_member hw.2.1 htc (by exact hidc.symm),hec]
  · intro event kind he
    obtain ⟨trace,ht,hid,_⟩ := Ordered.kindAt_trace he
    obtain ⟨h0,_⟩ | ⟨h1,_⟩ := completed_member_events hp hw hc ht
    · exact Or.inl (hid.symm.trans h0)
    · exact Or.inr (hid.symm.trans h1)

theorem dynamic_consumer_lookup (retries flagValue payloadValue serial : Nat) :
    (dynamicConsumerEvents retries flagValue payloadValue)[serial]? =
      if serial < retries then some (acquireEvent 0)
      else if serial = retries then some (acquireEvent flagValue)
      else if serial = retries+1 then some ((tailEvents payloadValue)[0]'(by simp [tailEvents]))
      else if serial = retries+2 then some ((tailEvents payloadValue)[1]'(by simp [tailEvents]))
      else none := by
  simp only [dynamicConsumerEvents,List.append_assoc]
  by_cases hlt : serial < retries
  · rw [List.getElem?_append_left (by simpa using hlt)]
    simp [hlt]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate]
    by_cases h0 : serial = retries
    · subst serial; simp [tailEvents]
    · by_cases h1 : serial = retries+1
      · subst serial; simp [tailEvents]
      · by_cases h2 : serial = retries+2
        · subst serial; simp [tailEvents]
        · have hn : ¬serial - retries < ([acquireEvent flagValue] ++ tailEvents payloadValue).length := by
            simp only [List.length_append,List.length_cons,List.length_nil,tailEvents]
            omega
          rw [List.getElem?_eq_none (by omega)]
          simp [hlt,h0,h1,h2]

namespace CompletedShape
variable {execution : Ordered.Candidate} {retries flagValue payloadValue : Nat}

theorem payload_write (hs : CompletedShape execution retries flagValue payloadValue) :
    execution.kindAt payloadWrite = some ⟨.write payload (Scalar.u32Bytes 42),.weak,none⟩ := hs.producer 0

theorem flag_write (hs : CompletedShape execution retries flagValue payloadValue) :
    execution.kindAt flagWrite = some ⟨.write flag (Scalar.u32Bytes 1),.release,some .gpu⟩ := hs.producer 1

theorem last_acquire (hs : CompletedShape execution retries flagValue payloadValue) :
    execution.kindAt (finalFlagRead retries) = some (acquireEvent flagValue) := by
  rw [finalFlagRead,hs.consumer,dynamic_consumer_lookup]
  simp

theorem payload_read (hs : CompletedShape execution retries flagValue payloadValue) :
    execution.kindAt (finalPayloadRead retries) = some ((tailEvents payloadValue)[0]'(by simp [tailEvents])) := by
  rw [finalPayloadRead,hs.consumer,dynamic_consumer_lookup]
  simp

theorem output_write (hs : CompletedShape execution retries flagValue payloadValue) :
    execution.kindAt (finalOutputWrite retries) = some ((tailEvents payloadValue)[1]'(by simp [tailEvents])) := by
  rw [finalOutputWrite,hs.consumer,dynamic_consumer_lookup]
  simp

theorem kind_cases (hs : CompletedShape execution retries flagValue payloadValue) {event kind}
    (he : execution.kindAt event = some kind) :
    (event = payloadWrite ∧ kind = producerEvents[0]) ∨
    (event = flagWrite ∧ kind = producerEvents[1]) ∨
    (event.thread = id 1 ∧ event.serial ≤ retries ∧ kind = acquireEvent (if event.serial < retries then 0 else flagValue)) ∨
    (event = finalPayloadRead retries ∧ kind = (tailEvents payloadValue)[0]'(by simp [tailEvents])) ∨
    (event = finalOutputWrite retries ∧ kind = (tailEvents payloadValue)[1]'(by simp [tailEvents])) := by
  rcases hs.threads event kind he with h0 | h1
  · have hp : execution.kindAt event = producerEvents[event.serial]? := by
      simpa only [← h0] using hs.producer event.serial
    rw [hp] at he
    cases hn : event.serial with
    | zero => exact Or.inl ⟨by cases event; simp_all [payloadWrite],by simpa [hn,producerEvents] using he.symm⟩
    | succ n =>
      cases n with
      | zero => exact Or.inr (Or.inl ⟨by cases event; simp_all [flagWrite],by simpa [hn,producerEvents] using he.symm⟩)
      | succ n => simp [hn,producerEvents] at he
  · have hp : execution.kindAt event = (dynamicConsumerEvents retries flagValue payloadValue)[event.serial]? := by
      simpa only [← h1] using hs.consumer event.serial
    rw [hp,dynamic_consumer_lookup] at he
    by_cases hlt : event.serial < retries
    · exact Or.inr (Or.inr (Or.inl ⟨h1,by omega,by simpa [hlt] using he.symm⟩))
    · by_cases h0 : event.serial = retries
      · exact Or.inr (Or.inr (Or.inl ⟨h1,by omega,by simpa [hlt,h0] using he.symm⟩))
      · by_cases hr : event.serial = retries+1
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by cases event; simp_all [finalPayloadRead],by simpa [hlt,h0,hr] using he.symm⟩)))
        · by_cases hw : event.serial = retries+2
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by cases event; simp_all [finalOutputWrite],by simpa [hlt,h0,hr,hw] using he.symm⟩)))
          · simp [hlt,h0,hr,hw] at he

theorem view_cases (hs : CompletedShape execution retries flagValue payloadValue) {event kind}
    (he : execution.view.eventAt event = some kind) :
    (event = payloadWrite ∧ kind = .write payload (Scalar.u32Bytes 42)) ∨
    (event = flagWrite ∧ kind = .write flag (Scalar.u32Bytes 1)) ∨
    (event.thread = id 1 ∧ event.serial ≤ retries ∧ kind = .read flag (Scalar.u32Bytes (word (if event.serial < retries then 0 else flagValue)))) ∨
    (event = finalPayloadRead retries ∧ kind = .read payload (Scalar.u32Bytes (word payloadValue))) ∨
    (event = finalOutputWrite retries ∧ kind = .write output (Scalar.u32Bytes (word payloadValue))) := by
  rw [Ordered.view_eventAt] at he
  obtain ⟨annotated,ha,hkind⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨ht,hi,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := hs.kind_cases ha
  all_goals simp_all [producerEvents,tailEvents,acquireEvent,output]

end CompletedShape
end
end Ptx.Kernels.ReleaseAcquireMessage
