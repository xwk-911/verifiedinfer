import Ptx.Kernels.ReleaseAcquireMessageSource
import Ptx.Ordered.Witnesses

/-! Exact event structure of the actual complete source candidate. No canonical
candidate is substituted into a universal correctness theorem. -/
namespace Ptx.Kernels.ReleaseAcquireMessage
open Ptx.ISA Ptx.Ordered
noncomputable section

def output : Location := ⟨.global,256⟩
def outputWrite : Ptx.Event.EventId := ⟨id 1,2⟩
def producerEvents : List Ordered.Kind := [
  ⟨.write payload (Scalar.u32Bytes 42),.weak,none⟩,
  ⟨.write flag (Scalar.u32Bytes 1),.release,some .gpu⟩]
def consumerEvents : List Ordered.Kind := [
  ⟨.read flag (Scalar.u32Bytes 1),.acquire,some .gpu⟩,
  ⟨.read payload (Scalar.u32Bytes 42),.weak,none⟩,
  ⟨.write output (Scalar.u32Bytes 42),.weak,none⟩]

theorem producer_source_events : (trace 0 9).events = producerEvents := rfl
theorem consumer_source_events : (trace 1 12).events = consumerEvents := rfl
theorem source_trace_id (tid count : Nat) : (trace tid count).id = id tid := rfl

theorem kind_at_cases {event kind} (he : candidate.kindAt event = some kind) :
    (event = payloadWrite ∧ kind = producerEvents[0]) ∨
    (event = flagWrite ∧ kind = producerEvents[1]) ∨
    (event = flagRead ∧ kind = consumerEvents[0]) ∨
    (event = payloadRead ∧ kind = consumerEvents[1]) ∨
    (event = outputWrite ∧ kind = consumerEvents[2]) := by
  by_cases h0 : event.thread = id 0
  · have h1 : id 1 ≠ event.thread := by rw [h0]; decide
    have hx : candidate.kindAt event = producerEvents[event.serial]? := by
      simp [Ordered.Candidate.kindAt,candidate,h0,source_trace_id,producer_source_events]
    rw [hx] at he
    cases hs : event.serial with
    | zero =>
      have hk : kind = producerEvents[0] := by simpa [hs,producerEvents] using he.symm
      exact Or.inl ⟨by cases event; simp_all [payloadWrite],hk⟩
    | succ n =>
      cases n with
      | zero =>
        have hk : kind = producerEvents[1] := by simpa [hs,producerEvents] using he.symm
        exact Or.inr (Or.inl ⟨by cases event; simp_all [flagWrite],hk⟩)
      | succ n => simp [hs,producerEvents] at he
  · by_cases h1 : event.thread = id 1
    · have hb0 : (id 0 == event.thread) = false := by
        cases hb : (id 0 == event.thread) with
        | false => rfl
        | true => exact False.elim (h0 (beq_iff_eq.mp hb).symm)
      have hb1 : (id 1 == event.thread) = true := beq_iff_eq.mpr h1.symm
      have hx : candidate.kindAt event = consumerEvents[event.serial]? := by
        simp only [Ordered.Candidate.kindAt,candidate,List.find?_cons,source_trace_id,hb0,hb1,
          Bool.false_eq_true,ite_false,ite_true,Option.bind_some,consumer_source_events]
      rw [hx] at he
      cases hs : event.serial with
      | zero =>
        have hk : kind = consumerEvents[0] := by simpa [hs,consumerEvents] using he.symm
        exact Or.inr (Or.inr (Or.inl ⟨by cases event; simp_all [flagRead],hk⟩))
      | succ n =>
        cases n with
        | zero =>
          have hk : kind = consumerEvents[1] := by simpa [hs,consumerEvents] using he.symm
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by cases event; simp_all [payloadRead],hk⟩)))
        | succ n =>
          cases n with
          | zero =>
            have hk : kind = consumerEvents[2] := by simpa [hs,consumerEvents] using he.symm
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by cases event; simp_all [outputWrite],hk⟩)))
          | succ n => simp [hs,consumerEvents] at he
    · have hb0 : (id 0 == event.thread) = false := by
        cases hb : (id 0 == event.thread) with
        | false => rfl
        | true => exact False.elim (h0 (beq_iff_eq.mp hb).symm)
      have hb1 : (id 1 == event.thread) = false := by
        cases hb : (id 1 == event.thread) with
        | false => rfl
        | true => exact False.elim (h1 (beq_iff_eq.mp hb).symm)
      simp only [Ordered.Candidate.kindAt,candidate,List.find?_cons,source_trace_id,hb0,hb1,
        Bool.false_eq_true,ite_false,List.find?_nil,Option.bind_none,reduceCtorEq] at he

theorem view_event_cases {event kind} (he : candidate.view.eventAt event = some kind) :
    (event = payloadWrite ∧ kind = .write payload (Scalar.u32Bytes 42)) ∨
    (event = flagWrite ∧ kind = .write flag (Scalar.u32Bytes 1)) ∨
    (event = flagRead ∧ kind = .read flag (Scalar.u32Bytes 1)) ∨
    (event = payloadRead ∧ kind = .read payload (Scalar.u32Bytes 42)) ∨
    (event = outputWrite ∧ kind = .write output (Scalar.u32Bytes 42)) := by
  rw [Ordered.view_eventAt] at he
  obtain ⟨annotated,ha,hkind⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := kind_at_cases ha
  all_goals simp_all [producerEvents,consumerEvents]

theorem only_release_tag {event} (he : (candidate.kindAt event).map Ordered.Kind.order = some .release) :
    event = flagWrite := by
  obtain ⟨kind,hk,htag⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := kind_at_cases hk
  all_goals simp_all [producerEvents,consumerEvents]

theorem only_acquire_tag {event} (he : (candidate.kindAt event).map Ordered.Kind.order = some .acquire) :
    event = flagRead := by
  obtain ⟨kind,hk,htag⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := kind_at_cases hk
  all_goals simp_all [producerEvents,consumerEvents]

def rank (event : Ptx.Event.EventId) : Nat := 3*event.thread.tid.x+event.serial

theorem program_order_rank {a b} (hp : Ptx.Event.ProgramOrder candidate.view a b) : rank a < rank b := by
  unfold rank
  rw [hp.2.2.1]
  have hserial := hp.2.2.2
  omega

theorem release_acquire_rank {a b} (hs : Ordered.ReleaseAcquireSync candidate rf a b) : rank a < rank b := by
  have ha := only_release_tag hs.1
  have hb := only_acquire_tag hs.2.1
  rw [ha,hb]
  decide

theorem no_barrier_returns {event bid generation} :
    candidate.view.eventAt event ≠ some (.barrierReturn bid generation) := by
  intro he
  obtain ⟨_,hk⟩ | ⟨_,hk⟩ | ⟨_,hk⟩ | ⟨_,hk⟩ | ⟨_,hk⟩ := view_event_cases he
  all_goals cases hk

end
end Ptx.Kernels.ReleaseAcquireMessage
