import Ptx.Hopper.WgmmaRules
import Ptx.Hopper.Source

/-! Number-preserving component views of rich WGMMA/Hopper executions. Every
source event occupies one slot, including all four WGMMA forms. Opaque tags
are not memory/resource/fence events. Projection does not prove the original
Hopper Produced predicate, whose interpreter deliberately rejects WGMMA. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

def eventView : Wgmma.Event → Hopper.Event
  | .base event => event
  | .fence _ => .wgmma .fence
  | .mma _ _ => .wgmma .mma
  | .commit _ _ => .wgmma .commit
  | .wait _ _ _ _ _ _ => .wgmma .wait
def locatedView (event : SourceRun.Located Wgmma.Event) : SourceRun.Located Hopper.Event :=
  ⟨eventView event.kind,event.pc⟩
structure ThreadTrace where
  id : ThreadId
  oracle : Wgmma.Oracle
  count : Nat
  final : Wgmma.State
  events : List Wgmma.Event
structure Candidate where
  traces : List ThreadTrace
def ThreadTrace.view (trace : ThreadTrace) : Hopper.ThreadTrace := {
  id := trace.id
  oracle := trace.oracle.base
  count := trace.count
  final := trace.final.base
  events := trace.events.map eventView
}
def Candidate.view (candidate : Candidate) : Hopper.Candidate := ⟨candidate.traces.map ThreadTrace.view⟩
def Candidate.traceAt (candidate : Candidate) (id : ThreadId) : Option ThreadTrace :=
  candidate.traces.find? (fun trace => trace.id == id)
def Candidate.eventAt (candidate : Candidate) (id : Ptx.Event.EventId) : Option Wgmma.Event :=
  (candidate.traceAt id.thread).bind (fun trace => trace.events[id.serial]?)
def Candidate.Present (candidate : Candidate) (id : Ptx.Event.EventId) : Prop := (candidate.eventAt id).isSome = true
instance (candidate id) : Decidable (Candidate.Present candidate id) := by unfold Candidate.Present; infer_instance

theorem view_trace_ids (candidate : Candidate) : candidate.view.traces.map Hopper.ThreadTrace.id = candidate.traces.map ThreadTrace.id := by
  simp only [Candidate.view,List.map_map,Function.comp_def,ThreadTrace.view]
theorem view_event_count (trace : ThreadTrace) : trace.view.events.length = trace.events.length := List.length_map _
theorem view_event_index (trace : ThreadTrace) (serial : Nat) :
    trace.view.events[serial]? = (trace.events[serial]?).map eventView := List.getElem?_map
theorem view_traceAt (candidate : Candidate) (id : ThreadId) :
    candidate.view.traceAt id = (candidate.traceAt id).map ThreadTrace.view := by
  unfold Hopper.Candidate.traceAt Candidate.view Candidate.traceAt
  induction candidate.traces with
  | nil => rfl
  | cons trace rest ih =>
    simp only [List.map_cons,List.find?_cons,ThreadTrace.view]
    split <;> simp_all [ThreadTrace.view]
theorem view_eventAt (candidate : Candidate) (id : Ptx.Event.EventId) :
    candidate.view.eventAt id = (candidate.eventAt id).map eventView := by
  simp only [Hopper.Candidate.eventAt,view_traceAt,Candidate.eventAt]
  cases ht : candidate.traceAt id.thread <;> simp [ht,ThreadTrace.view,List.getElem?_map]
theorem view_present_iff (candidate : Candidate) (id : Ptx.Event.EventId) :
    candidate.view.Present id ↔ candidate.Present id := by
  simp only [Hopper.Candidate.Present,Candidate.Present,view_eventAt,Option.isSome_map]
theorem located_view_pc (event : SourceRun.Located Wgmma.Event) : (locatedView event).pc = event.pc := rfl
theorem located_view_erasure (events : List (SourceRun.Located Wgmma.Event)) :
    (events.map locatedView).map SourceRun.Located.kind = (events.map SourceRun.Located.kind).map eventView := by
  simp only [List.map_map,Function.comp_def,locatedView]

theorem view_base_iff {event : Wgmma.Event} {base : Hopper.Event}
    (hn : ∀ tag, base ≠ .wgmma tag) : eventView event = base ↔ event = .base base := by
  cases event <;> simp only [eventView] <;> constructor <;> intro h
  all_goals first | cases h; rfl | exact (hn _ h.symm).elim | cases h
theorem view_tma_iff {candidate : Candidate} {id copy} :
    candidate.view.eventAt id = some (.tmaIssue copy) ↔ candidate.eventAt id = some (.base (.tmaIssue copy)) := by
  rw [view_eventAt]
  cases he : candidate.eventAt id with
  | none => simp
  | some event =>
    simp only [Option.map_some,Option.some.injEq]
    exact view_base_iff (fun tag h => by cases h)
theorem view_barrier_iff {candidate : Candidate} {id barrier} :
    candidate.view.eventAt id = some (.barrier barrier) ↔ candidate.eventAt id = some (.base (.barrier barrier)) := by
  rw [view_eventAt]
  cases he : candidate.eventAt id with
  | none => simp
  | some event =>
    simp only [Option.map_some,Option.some.injEq]
    exact view_base_iff (fun tag h => by cases h)

end
end Ptx.Hopper.Unified
