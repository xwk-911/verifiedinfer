import Ptx.Shuffle.Execution
import Ptx.Shuffle.Trace

/-! Lookups of actual source-produced shuffle traces. Event indices refer to
the original emitted trace, before the ordinary-memory projection. -/
namespace Ptx.Shuffle
open Ptx.ISA
noncomputable section

theorem unique_trace_id {traces : List ThreadTrace} (hn : (traces.map ThreadTrace.id).Nodup)
    {left right : ThreadTrace} (hl : left ∈ traces) (hr : right ∈ traces) (hi : left.id = right.id) : left = right := by
  induction traces with
  | nil => simp at hl
  | cons first rest ih =>
    simp only [List.map_cons,List.nodup_cons] at hn
    simp only [List.mem_cons] at hl hr
    rcases hl with rfl | hl <;> rcases hr with rfl | hr
    · rfl
    · exact (hn.1 (List.mem_map.mpr ⟨right,hr,hi.symm⟩)).elim
    · exact (hn.1 (List.mem_map.mpr ⟨left,hl,hi⟩)).elim
    · exact ih hn.2 hl hr

theorem eventAt_of_member {candidate : Candidate} {trace : ThreadTrace} {id : Event.EventId}
    (hn : (candidate.traces.map ThreadTrace.id).Nodup) (ht : trace ∈ candidate.traces) (hid : id.thread = trace.id) :
    candidate.eventAt id = trace.events[id.serial]? := by
  unfold Candidate.eventAt
  cases hf : candidate.traces.find? (fun other => other.id == id.thread) with
  | none => have hh := List.find?_eq_none.mp hf trace ht; simp [hid] at hh
  | some other =>
    have hm := List.mem_of_find?_eq_some hf
    have hi : other.id = id.thread := by simpa only [beq_iff_eq] using List.find?_some hf
    have he := unique_trace_id hn ht hm (hid.symm.trans hi.symm)
    subst other
    rfl

theorem eventAt_trace {candidate : Candidate} {id event} (he : candidate.eventAt id = some event) :
    ∃ trace ∈ candidate.traces, trace.id = id.thread ∧ trace.events[id.serial]? = some event := by
  unfold Candidate.eventAt at he
  cases hf : candidate.traces.find? (fun trace => trace.id == id.thread) with
  | none => simp [hf] at he
  | some trace => exact ⟨trace,List.mem_of_find?_eq_some hf,
      by simpa only [beq_iff_eq] using List.find?_some hf,
      by simpa only [hf,Option.bind_some] using he⟩

theorem shuffleAt_eventAt {candidate : Candidate} {id record} (he : candidate.shuffleAt id = some record) :
    candidate.eventAt id = some (.shuffle record) := by
  unfold Candidate.shuffleAt at he
  cases hx : candidate.eventAt id with
  | none => simp [hx] at he
  | some event =>
    cases event with
    | ordinary _ => simp [hx] at he
    | shuffle other =>
      have hr : other = record := by simpa only [hx,Option.bind_some,Option.some.injEq] using he
      cases hr
      rfl

/-- The ordinary graph renumbers events after filtering shuffle records. Its
serial index must not be confused with the original source-event index. -/
theorem view_eventAt_of_member {candidate : Candidate} {trace : ThreadTrace} {id : Event.EventId}
    (hn : (candidate.traces.map ThreadTrace.id).Nodup) (ht : trace ∈ candidate.traces) (hid : id.thread = trace.id) :
    candidate.view.eventAt id = (ordinaryEvents trace.events)[id.serial]? := by
  have hu : (candidate.view.traces.map Event.ThreadTrace.id).Nodup := by rw [view_thread_ids]; exact hn
  exact Event.eventAt_of_trace hu (List.mem_map.mpr ⟨trace,ht,rfl⟩) hid

end
end Ptx.Shuffle
