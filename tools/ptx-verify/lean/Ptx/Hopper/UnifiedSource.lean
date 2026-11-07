import Ptx.Hopper.UnifiedView

/-! One source-checked entry for TMA, WGMMA and ordinary instructions. Rich
events remain authoritative. The number-preserving view is consumed by legacy
resource/memory components, without asserting legacy Hopper.Produced. Source
completion additionally requires an empty pending WGMMA ledger. This module
does not supply collective, weak-memory/RF, allocation or runtime admission. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

def Produced (code : List Instr) (params : Bindings) (block : Dim3) (trace : ThreadTrace) : Prop :=
  Wgmma.run {id := trace.id,params := params,block := block} trace.oracle code trace.count {} = .ok (trace.final,trace.events)
def WellFormed (code : List Instr) (launch : Scalar.Launch) (candidate : Candidate) : Prop :=
  launch.geometry.Valid ∧ (candidate.traces.map ThreadTrace.id).Nodup ∧
  (∀ trace ∈ candidate.traces, trace.id.Valid launch.geometry ∧ Produced code launch.params launch.geometry.block trace) ∧
  ∀ id, id.Valid launch.geometry → ∃ trace ∈ candidate.traces, trace.id = id
def Complete (candidate : Candidate) : Prop := ∀ trace ∈ candidate.traces, Wgmma.Complete trace.final
def Candidate.sourceAt (candidate : Candidate) (code : List Instr) (params : Bindings) (block : Dim3)
    (id : Ptx.Event.EventId) : Option (SourceRun.Located Wgmma.Event) :=
  (candidate.traceAt id.thread).bind (fun trace =>
    (Wgmma.runLocated {id := trace.id,params := params,block := block} trace.oracle code trace.count {}).toOption.bind
      (fun result => result.2[id.serial]?))
def Candidate.sourcePC (candidate : Candidate) (code : List Instr) (params : Bindings) (block : Dim3)
    (id : Ptx.Event.EventId) : Option Nat :=
  (candidate.sourceAt code params block id).map SourceRun.Located.pc
def Candidate.componentSourceAt (candidate : Candidate) (code : List Instr) (params : Bindings) (block : Dim3)
    (id : Ptx.Event.EventId) : Option (SourceRun.Located Hopper.Event) :=
  (candidate.sourceAt code params block id).map locatedView

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
theorem traceAt_of_member {candidate : Candidate} {trace : ThreadTrace}
    (hn : (candidate.traces.map ThreadTrace.id).Nodup) (ht : trace ∈ candidate.traces) :
    candidate.traceAt trace.id = some trace := by
  unfold Candidate.traceAt
  cases hf : candidate.traces.find? (fun other => other.id == trace.id) with
  | none => have hh := List.find?_eq_none.mp hf trace ht; simp at hh
  | some other =>
    have hm := List.mem_of_find?_eq_some hf
    have hi : other.id = trace.id := by simpa only [beq_iff_eq] using List.find?_some hf
    have he := unique_trace_id hn ht hm hi.symm
    subst other
    rfl
theorem eventAt_of_member {candidate : Candidate} {trace : ThreadTrace}
    (hn : (candidate.traces.map ThreadTrace.id).Nodup) (ht : trace ∈ candidate.traces) (serial : Nat) :
    candidate.eventAt ⟨trace.id,serial⟩ = trace.events[serial]? := by
  simp [Candidate.eventAt,traceAt_of_member hn ht]
theorem eventAt_trace {candidate : Candidate} {id event} (he : candidate.eventAt id = some event) :
    ∃ trace ∈ candidate.traces, trace.id = id.thread ∧ trace.events[id.serial]? = some event := by
  unfold Candidate.eventAt at he
  cases ht : candidate.traceAt id.thread with
  | none => simp [ht] at he
  | some trace => exact ⟨trace,List.mem_of_find?_eq_some ht,
      by simpa only [beq_iff_eq] using List.find?_some ht,
      by simpa only [ht,Option.bind_some] using he⟩
theorem sourceAt_of_member {candidate : Candidate} {trace : ThreadTrace} {id : Ptx.Event.EventId} {code params block}
    (hn : (candidate.traces.map ThreadTrace.id).Nodup) (ht : trace ∈ candidate.traces) (hid : id.thread = trace.id) :
    candidate.sourceAt code params block id =
      (Wgmma.runLocated {id := trace.id,params := params,block := block} trace.oracle code trace.count {}).toOption.bind
        (fun result => result.2[id.serial]?) := by
  unfold Candidate.sourceAt
  rw [hid,traceAt_of_member hn ht]
  rfl
theorem source_event {candidate : Candidate} {code launch id event}
    (hw : WellFormed code launch candidate) (he : candidate.eventAt id = some event) :
    ∃ located, candidate.sourceAt code launch.params launch.geometry.block id = some located ∧ located.kind = event ∧
      ∃ oracle before after emitted,
        Wgmma.step {id := id.thread,params := launch.params,block := launch.geometry.block} oracle code before = .ok (after,emitted) ∧
        event ∈ emitted ∧ located.pc = before.base.scalar.core.thread.pc := by
  unfold Candidate.eventAt at he
  cases ht : candidate.traceAt id.thread with
  | none => simp [ht] at he
  | some trace =>
    have hm := List.mem_of_find?_eq_some ht
    have hid : trace.id = id.thread := by simpa only [beq_iff_eq] using List.find?_some ht
    have hx : trace.events[id.serial]? = some event := by simpa only [ht,Option.bind_some] using he
    obtain ⟨located,hr,herase⟩ := Wgmma.run_located_exists (hw.2.2.1 trace hm).2
    rw [← herase,List.getElem?_map] at hx
    cases hs : located[id.serial]? with
    | none => simp [hs] at hx
    | some source =>
      have hk : source.kind = event := by simpa [hs] using hx
      refine ⟨source,?_,hk,?_⟩
      · simp only [Candidate.sourceAt,ht,Option.bind_some,hr,Except.toOption,Option.bind_some]
        exact hs
      · obtain ⟨before,after,emitted,hstep,hemitted,hpc⟩ := SourceRun.event_origin hr hs
        exact ⟨trace.oracle,before,after,emitted,by simpa only [hid] using hstep,hk ▸ hemitted,hpc⟩
theorem component_source_event {candidate : Candidate} {code launch id event}
    (hw : WellFormed code launch candidate) (he : candidate.eventAt id = some event) :
    ∃ located, candidate.componentSourceAt code launch.params launch.geometry.block id = some located ∧
      located.kind = eventView event ∧ candidate.sourcePC code launch.params launch.geometry.block id = some located.pc := by
  obtain ⟨located,hs,hk,_⟩ := source_event hw he
  exact ⟨locatedView located,by simp only [Candidate.componentSourceAt,hs,Option.map_some],
    by simp only [locatedView,hk],by simp only [Candidate.sourcePC,hs,Option.map_some,locatedView]⟩
theorem view_complete {candidate : Candidate} (hc : Complete candidate) : Hopper.Complete candidate.view := by
  intro trace ht
  obtain ⟨rich,hm,rfl⟩ := List.mem_map.mp ht
  exact (hc rich hm).1
theorem view_ids_unique {candidate : Candidate} {code launch} (hw : WellFormed code launch candidate) :
    (candidate.view.traces.map Hopper.ThreadTrace.id).Nodup := by
  rw [view_trace_ids]
  exact hw.2.1
theorem view_geometry_and_coverage {candidate : Candidate} {code launch} (hw : WellFormed code launch candidate) :
    launch.geometry.Valid ∧
      (∀ trace ∈ candidate.view.traces, trace.id.Valid launch.geometry) ∧
      ∀ id, id.Valid launch.geometry → ∃ trace ∈ candidate.view.traces, trace.id = id := by
  refine ⟨hw.1,?_,?_⟩
  · intro trace ht
    obtain ⟨rich,hm,rfl⟩ := List.mem_map.mp ht
    exact (hw.2.2.1 rich hm).1
  · intro id hi
    obtain ⟨trace,ht,he⟩ := hw.2.2.2 id hi
    exact ⟨trace.view,List.mem_map.mpr ⟨trace,ht,rfl⟩,he⟩

end
end Ptx.Hopper.Unified
