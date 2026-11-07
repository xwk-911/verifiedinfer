import Ptx.Ordered.Execution

/-! Source-member lookup with arbitrary candidate order. Ordered event indices
are preserved by the ordinary projection; no shuffle filtering occurs. -/
namespace Ptx.Ordered
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

theorem kindAt_of_member {candidate : Candidate} {trace : ThreadTrace} {id : Event.EventId}
    (hn : (candidate.traces.map ThreadTrace.id).Nodup) (ht : trace ∈ candidate.traces) (hid : id.thread = trace.id) :
    candidate.kindAt id = trace.events[id.serial]? := by
  unfold Candidate.kindAt
  cases hf : candidate.traces.find? (fun other => other.id == id.thread) with
  | none => have hh := List.find?_eq_none.mp hf trace ht; simp [hid] at hh
  | some other =>
    have hm := List.mem_of_find?_eq_some hf
    have hi : other.id = id.thread := by simpa only [beq_iff_eq] using List.find?_some hf
    have he := unique_trace_id hn ht hm (hid.symm.trans hi.symm)
    subst other
    rfl

theorem kindAt_trace {candidate : Candidate} {id event} (he : candidate.kindAt id = some event) :
    ∃ trace ∈ candidate.traces, trace.id = id.thread ∧ trace.events[id.serial]? = some event := by
  unfold Candidate.kindAt at he
  cases hf : candidate.traces.find? (fun trace => trace.id == id.thread) with
  | none => simp [hf] at he
  | some trace => exact ⟨trace,List.mem_of_find?_eq_some hf,
      by simpa only [beq_iff_eq] using List.find?_some hf,
      by simpa only [hf,Option.bind_some] using he⟩

end
end Ptx.Ordered
