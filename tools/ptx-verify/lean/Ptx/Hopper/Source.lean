import Ptx.Hopper.Thread
import Ptx.Event.Relations

/-! Launch-wide actual Hopper source candidates. Provenance/coverage/completion
are separate from resource protocols, memory consistency, proxies and ISA UB. -/
namespace Ptx.Hopper
open Ptx.ISA
noncomputable section

structure ThreadTrace where
  id : ThreadId
  oracle : Oracle
  count : Nat
  final : State
  events : List Event
structure Candidate where
  traces : List ThreadTrace

def Produced (code : List Instr) (params : Bindings) (block : Dim3) (t : ThreadTrace) : Prop :=
  run {id := t.id,params := params,block := block} t.oracle code t.count {} = .ok (t.final,t.events)
def WellFormed (code : List Instr) (launch : Scalar.Launch) (c : Candidate) : Prop :=
  launch.geometry.Valid ∧ (c.traces.map ThreadTrace.id).Nodup ∧
  (∀ t ∈ c.traces, t.id.Valid launch.geometry ∧ Produced code launch.params launch.geometry.block t) ∧
  ∀ id, id.Valid launch.geometry → ∃ t ∈ c.traces, t.id = id
def Complete (c : Candidate) : Prop := ∀ t ∈ c.traces, t.final.scalar.core.thread.status = .done

def Candidate.traceAt (c : Candidate) (id : ThreadId) : Option ThreadTrace :=
  c.traces.find? (fun t => t.id == id)
def Candidate.eventAt (c : Candidate) (id : Ptx.Event.EventId) : Option Event :=
  (c.traceAt id.thread).bind (fun t => t.events[id.serial]?)
def Candidate.Present (c : Candidate) (id : Ptx.Event.EventId) : Prop := (c.eventAt id).isSome = true
instance (c id) : Decidable (Candidate.Present c id) := by unfold Candidate.Present; infer_instance

def Candidate.barrierAt (c : Candidate) (id : Ptx.Event.EventId) : Option BarrierEvent :=
  (c.eventAt id).bind (fun e => match e with | .barrier b => some b | _ => none)

def Candidate.sourceAt (c : Candidate) (code : List Instr) (params : Bindings) (block : Dim3) (id : Ptx.Event.EventId) :
    Option (SourceRun.Located Event) :=
  (c.traceAt id.thread).bind (fun t =>
    ((runLocated {id := t.id,params := params,block := block} t.oracle code t.count {}).toOption).bind
      (fun result => result.2[id.serial]?))
def sourcePC (c : Candidate) (code : List Instr) (params : Bindings) (block : Dim3) (id : Ptx.Event.EventId) : Option Nat :=
  (c.sourceAt code params block id).map SourceRun.Located.pc

theorem unique_trace_id {traces : List ThreadTrace} (hn : (traces.map ThreadTrace.id).Nodup)
    {t u : ThreadTrace} (ht : t ∈ traces) (hu : u ∈ traces) (hid : t.id = u.id) : t = u := by
  induction traces with
  | nil => simp at ht
  | cons first rest ih =>
    simp only [List.map_cons,List.nodup_cons] at hn
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

theorem eventAt_of_member {c : Candidate} {t : ThreadTrace} (hn : (c.traces.map ThreadTrace.id).Nodup)
    (ht : t ∈ c.traces) (serial : Nat) : c.eventAt ⟨t.id,serial⟩ = t.events[serial]? := by
  simp [Candidate.eventAt,traceAt_of_member hn ht]

theorem eventAt_trace {c : Candidate} {event kind} (he : c.eventAt event = some kind) :
    ∃ t ∈ c.traces, t.id = event.thread ∧ t.events[event.serial]? = some kind := by
  unfold Candidate.eventAt at he
  cases ht : c.traceAt event.thread with
  | none => simp [ht] at he
  | some t =>
    exact ⟨t,List.mem_of_find?_eq_some ht,
      by simpa only [beq_iff_eq] using List.find?_some ht,
      by simpa only [ht,Option.bind_some] using he⟩

theorem barrierAt_iff {c : Candidate} {event data} : c.barrierAt event = some data ↔ c.eventAt event = some (.barrier data) := by
  cases he : c.eventAt event with
  | none => simp [Candidate.barrierAt,he]
  | some kind => cases kind <;> simp [Candidate.barrierAt,he]

theorem barrier_present {c : Candidate} {event data} (he : c.barrierAt event = some data) : c.Present event := by
  simp [Candidate.Present,barrierAt_iff.mp he]

theorem sourceAt_of_member {c : Candidate} {t : ThreadTrace} {id : Ptx.Event.EventId} {code params block}
    (hn : (c.traces.map ThreadTrace.id).Nodup) (ht : t ∈ c.traces) (hid : id.thread = t.id) :
    c.sourceAt code params block id =
      (runLocated {id := t.id,params := params,block := block} t.oracle code t.count {}).toOption.bind (fun result => result.2[id.serial]?) := by
  unfold Candidate.sourceAt
  rw [hid,traceAt_of_member hn ht]
  rfl

theorem source_event {c : Candidate} {code launch id kind}
    (hw : WellFormed code launch c) (he : c.eventAt id = some kind) :
    ∃ located, c.sourceAt code launch.params launch.geometry.block id = some located ∧ located.kind = kind ∧
      ∃ oracle before after emitted, step {id := id.thread,params := launch.params,block := launch.geometry.block} oracle
        code before = .ok (after,emitted) ∧ kind ∈ emitted ∧ located.pc = before.scalar.core.thread.pc := by
  unfold Candidate.eventAt at he
  cases ht : c.traceAt id.thread with
  | none => simp [ht] at he
  | some t =>
    have hmem := List.mem_of_find?_eq_some ht
    have hid : t.id = id.thread := by simpa only [beq_iff_eq] using List.find?_some ht
    have hindex : t.events[id.serial]? = some kind := by simpa only [ht,Option.bind_some] using he
    obtain ⟨located,hr,herase⟩ := run_located_exists (hw.2.2.1 t hmem).2
    rw [← herase,List.getElem?_map] at hindex
    cases hs : located[id.serial]? with
    | none => simp [hs] at hindex
    | some source =>
      have hk : source.kind = kind := by simpa [hs] using hindex
      refine ⟨source,?_,hk,?_⟩
      · simp only [Candidate.sourceAt,ht,Option.bind_some,hr,Except.toOption,Option.bind_some]
        exact hs
      · obtain ⟨before,after,emitted,hstep,hsource,hpc⟩ := SourceRun.event_origin hr hs
        exact ⟨t.oracle,before,after,emitted,by simpa only [hid] using hstep,hk ▸ hsource,hpc⟩

end
end Ptx.Hopper
