import Ptx.Ampere.Graph
import Ptx.Ampere.Rules

/-! Actual source emission and final ledger agree. Augmented copies cannot be
invented by supplying an unrelated copy table in an admitted source candidate. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

theorem eventAt_trace {c : Candidate} {event kind} (he : c.eventAt event = some kind) :
    ∃ t ∈ c.traces, t.id = event.thread ∧ t.events[event.serial]? = some kind := by
  unfold Candidate.eventAt at he
  cases ht : c.traceAt event.thread with
  | none => simp [ht] at he
  | some t =>
    exact ⟨t,List.mem_of_find?_eq_some ht,
      by simpa only [beq_iff_eq] using List.find?_some ht,
      by simpa only [ht,Option.bind_some] using he⟩

theorem copyAt_trace {c : Candidate} {operation op} (he : c.copyAt operation = some op) :
    ∃ t ∈ c.traces, t.id = operation.thread ∧ t.final.copies[operation.ordinal]? = some op := by
  unfold Candidate.copyAt at he
  cases ht : c.traceAt operation.thread with
  | none => simp [ht] at he
  | some t =>
    exact ⟨t,List.mem_of_find?_eq_some ht,
      by simpa only [beq_iff_eq] using List.find?_some ht,
      by simpa only [ht,Option.bind_some] using he⟩

theorem unique_trace_id {traces : List ThreadTrace} (hn : (traces.map ThreadTrace.id).Nodup)
    {t u : ThreadTrace} (ht : t ∈ traces) (hu : u ∈ traces) (hid : t.id = u.id) : t = u := by
  induction traces with
  | nil => simp at ht
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at ht hu
    rcases ht with rfl | ht <;> rcases hu with rfl | hu
    · rfl
    · exact (hn.1 (List.mem_map.mpr ⟨u,hu,hid.symm⟩)).elim
    · exact (hn.1 (List.mem_map.mpr ⟨t,ht,hid⟩)).elim
    · exact ih hn.2 ht hu

theorem traceAt_of_member {c : Candidate} {t : ThreadTrace}
    (hn : (c.traces.map ThreadTrace.id).Nodup) (ht : t ∈ c.traces) : c.traceAt t.id = some t := by
  unfold Candidate.traceAt
  cases hf : c.traces.find? (fun x => x.id == t.id) with
  | none => have hh := List.find?_eq_none.mp hf t ht; simp at hh
  | some u =>
    have hu := List.mem_of_find?_eq_some hf
    have hid : u.id = t.id := by simpa only [beq_iff_eq] using List.find?_some hf
    have he := unique_trace_id hn ht hu hid.symm
    subst u
    rfl

theorem issued_copy_in_final_ledger {code params block t ordinal op}
    (hp : Produced code params block t) (he : Event.issue ordinal op ∈ t.events) :
    t.final.copies[ordinal]? = some op := (run_evolution hp).recorded ordinal op he

theorem final_copy_was_issued {code params block t ordinal op}
    (hp : Produced code params block t) (he : t.final.copies[ordinal]? = some op) :
    Event.issue ordinal op ∈ t.events := by
  rcases (run_evolution hp).origins ordinal op he with hnil | hsource
  · simp at hnil
  · exact hsource

theorem event_issue_has_copy {code launch c event ordinal op}
    (hw : WellFormed code launch c) (he : c.eventAt event = some (.issue ordinal op)) :
    c.copyAt ⟨event.thread,ordinal⟩ = some op := by
  unfold Candidate.eventAt at he
  cases ht : c.traceAt event.thread with
  | none => simp [ht] at he
  | some t =>
    have hmem := List.mem_of_find?_eq_some ht
    have hid : t.id = event.thread := by simpa only [beq_iff_eq] using List.find?_some ht
    have hindex : t.events[event.serial]? = some (.issue ordinal op) := by simpa only [ht,Option.bind_some] using he
    have hget := issued_copy_in_final_ledger (hw.2.2.1 t hmem).2 (List.mem_of_getElem? hindex)
    simpa only [Candidate.copyAt,ht,Option.bind_some] using hget

theorem copy_has_source_issue {code launch c operation op}
    (hw : WellFormed code launch c) (hc : c.copyAt operation = some op) :
    ∃ serial, c.eventAt ⟨operation.thread,serial⟩ = some (.issue operation.ordinal op) := by
  unfold Candidate.copyAt at hc
  cases ht : c.traceAt operation.thread with
  | none => simp [ht] at hc
  | some t =>
    have hmem := List.mem_of_find?_eq_some ht
    have hindex : t.final.copies[operation.ordinal]? = some op := by simpa only [ht,Option.bind_some] using hc
    obtain ⟨serial,he⟩ := List.mem_iff_getElem?.mp (final_copy_was_issued (hw.2.2.1 t hmem).2 hindex)
    exact ⟨serial,by simpa only [Candidate.eventAt,ht,Option.bind_some] using he⟩

end
end Ptx.Ampere
