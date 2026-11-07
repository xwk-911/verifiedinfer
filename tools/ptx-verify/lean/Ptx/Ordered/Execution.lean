import Ptx.Ordered.Thread
import Ptx.Scalar.Execution
import Ptx.Event.Observation

namespace Ptx.Ordered
open Ptx.ISA
noncomputable section

structure ThreadTrace where
  id : ThreadId
  oracle : Oracle
  count : Nat
  final : State
  events : List Kind
structure Candidate where
  traces : List ThreadTrace

def Produced (code : List Instr) (params : Bindings) (block : Dim3) (trace : ThreadTrace) : Prop :=
  run {id := trace.id,params := params,block := block} trace.oracle code trace.count {} = .ok (trace.final,trace.events)
def WellFormed (code : List Instr) (launch : Scalar.Launch) (candidate : Candidate) : Prop :=
  launch.geometry.Valid ∧ (candidate.traces.map ThreadTrace.id).Nodup ∧
  (∀ trace ∈ candidate.traces, trace.id.Valid launch.geometry ∧ Produced code launch.params launch.geometry.block trace) ∧
  ∀ id, id.Valid launch.geometry → ∃ trace ∈ candidate.traces, trace.id = id
def Complete (candidate : Candidate) : Prop := ∀ trace ∈ candidate.traces, trace.final.core.thread.status = .done

def Candidate.kindAt (candidate : Candidate) (id : Event.EventId) : Option Kind :=
  (candidate.traces.find? (fun trace => trace.id == id.thread)).bind (fun trace => trace.events[id.serial]?)
def Candidate.view (candidate : Candidate) : Scalar.Candidate :=
  ⟨candidate.traces.map fun trace => ⟨trace.id,trace.oracle,trace.count,trace.final.core,trace.events.map Kind.event⟩⟩

theorem produced_scalar_projection {code params block trace} (hp : Produced code params block trace) :
    Scalar.Produced (scalarSkeleton code) params
      ⟨trace.id,trace.oracle,trace.count,trace.final.core,trace.events.map Kind.event⟩ block :=
  ⟨trace.final.floats,run_preserves_scalar_events hp⟩

theorem view_complete {candidate : Candidate} (hc : Complete candidate) : candidate.view.Complete := by
  intro trace ht
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp ht
  exact hc original ho

/-- Local trace provenance only; ordered memory consistency is not erased to
the old weak memory predicates by this projection. -/
theorem scalar_well_formed_projection {code launch candidate} (hw : WellFormed code launch candidate) :
    Scalar.WellFormed (scalarSkeleton code) launch candidate.view := by
  refine ⟨hw.1,?_,?_,?_⟩
  · simpa only [Candidate.view,List.map_map,Function.comp_def] using hw.2.1
  · intro trace ht
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp ht
    exact ⟨(hw.2.2.1 original ho).1,produced_scalar_projection (hw.2.2.1 original ho).2⟩
  · intro thread hi
    obtain ⟨trace,ht,hid⟩ := hw.2.2.2 thread hi
    exact ⟨_,List.mem_map.mpr ⟨trace,ht,rfl⟩,hid⟩

theorem view_eventAt (candidate : Candidate) (id : Event.EventId) :
    candidate.view.eventAt id = (candidate.kindAt id).map Kind.event := by
  rcases candidate with ⟨traces⟩
  induction traces with
  | nil => rfl
  | cons trace traces ih =>
    simp only [Candidate.view,Event.Candidate.eventAt,Candidate.kindAt,List.map_cons,List.find?_cons]
    by_cases hi : trace.id == id.thread
    · simp [hi,List.getElem?_map]
    · simpa only [Candidate.view,Event.Candidate.eventAt,Candidate.kindAt,hi,Bool.false_eq_true,ite_false] using ih

end
end Ptx.Ordered
