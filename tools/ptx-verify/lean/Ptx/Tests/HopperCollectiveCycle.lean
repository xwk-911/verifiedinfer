import Ptx.Hopper.UnifiedControl
import Ptx.Generated.HopperCollectiveCycle
import Ptx.Kernels.HopperStageCollective

/-! Actual generated circular-wait source. Local traces finish and full aligned
schedules agree; the combined native/CTA control graph nevertheless cycles.
This refutes construct admission, not a hardware termination theorem. Never
launch this fixture on a GPU. Geometry here is the actual 3-D (4,8,4) cohort.
-/
namespace Ptx.HopperCollectiveCycleTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def oracle : Wgmma.Oracle := {base := {ampere := {scalar := fun _ => .integer 0,bytes := fun _ => []},wait := fun _ => false}}
def result (lane : Wgmma.Lane) : Wgmma.State × List Wgmma.Event :=
  (Wgmma.run (HopperStage.ctx lane) oracle Generated.hopper_collective_cycle.program 7 {}).toOption.getD ({},[])
def trace (lane : Wgmma.Lane) : Unified.ThreadTrace := ⟨(HopperStage.ctx lane).id,oracle,7,(result lane).1,(result lane).2⟩
def candidate : Unified.Candidate := ⟨List.ofFn trace⟩
def launch : Scalar.Launch := HopperStage.launch (fun _ => .bits (byte 165))
def eid (lane : Wgmma.Lane) (serial : Nat) : Ptx.Event.EventId := ⟨(HopperStage.ctx lane).id,serial⟩

theorem all_runs_succeed : ∀ lane : Wgmma.Lane,
    (Wgmma.run (HopperStage.ctx lane) oracle Generated.hopper_collective_cycle.program 7 {}).toOption.isSome = true := by decide
theorem all_complete_metadata : ∀ lane : Wgmma.Lane,
    (((result lane).1.base.scalar.core.thread.status == .done) && ((Wgmma.pending (result lane).1.ledger).length == 0)) = true := by decide
theorem source_produced (lane : Wgmma.Lane) :
    Unified.Produced Generated.hopper_collective_cycle.program HopperStage.params HopperStage.block (trace lane) := by
  change Wgmma.run (HopperStage.ctx lane) oracle Generated.hopper_collective_cycle.program 7 {} = .ok (result lane)
  cases hs : Wgmma.run (HopperStage.ctx lane) oracle Generated.hopper_collective_cycle.program 7 {} with
  | error fault => have hh := all_runs_succeed lane; rw [hs] at hh; cases hh
  | ok value => simp only [result,hs,Except.toOption,Option.getD_some]
theorem source_complete : Unified.Complete candidate := by
  intro actual ht
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  exact Wgmma.complete_of_metadata _ (all_complete_metadata lane)
theorem trace_ids_unique : (candidate.traces.map Unified.ThreadTrace.id).Nodup := by
  simpa only [candidate,List.map_ofFn,Function.comp_def,trace] using
    (show (List.ofFn (fun lane : Wgmma.Lane => (HopperStage.ctx lane).id)).Nodup from by decide)
theorem source_well_formed : Unified.WellFormed Generated.hopper_collective_cycle.program launch candidate := by
  refine ⟨?_,trace_ids_unique,?_,?_⟩
  · simp [launch,HopperStage.launch,HopperStage.geometry,HopperStage.block,Geometry.Valid,Dim3.Positive,Dim3.one]
  · intro actual ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨HopperStage.ctx_valid lane,source_produced lane⟩
  · intro id hi
    obtain ⟨lane,he⟩ := HopperStage.ctx_covered hi
    exact ⟨trace lane,List.mem_ofFn.mpr ⟨lane,rfl⟩,he⟩
theorem all_trace_schedule : ∀ lane : Wgmma.Lane,
    (trace lane).nativeSchedule = [⟨4,⟨4,0,0⟩,.fence⟩] := by decide
theorem schedules_match : Unified.SchedulesAdmitted HopperStage.block candidate := by
  apply Unified.schedules_admitted_of_participants
  intro actual ht _ lane
  obtain ⟨original,rfl⟩ := List.mem_ofFn.mp ht
  refine ⟨trace lane,List.mem_ofFn.mpr ⟨lane,rfl⟩,rfl,?_,?_⟩
  · change Ampere.linearThread (HopperStage.ctx lane) = 128*(Ampere.linearThread (HopperStage.ctx original)/128)+lane.val
    rw [HopperStage.ctx_linear,HopperStage.ctx_linear,Nat.div_eq_of_lt original.isLt]
    omega
  · simp only [Unified.ThreadTrace.alignedSchedule,all_trace_schedule]
theorem peer_return_before_native : Hopper.ProgramOrder candidate.view (eid 1 1) (eid 1 2) := by decide
theorem actual_same_warp_sync : Unified.NativeSync HopperStage.block candidate (eid 1 2) (eid 0 0) := by
  exact ⟨by decide,⟨4,⟨4,0,0⟩,.fence⟩,by decide,by decide⟩
theorem actual_back_path (histories : Location → List Tma.Entry) :
    Ptx.Event.Path (Tma.ControlEdge candidate.view histories) (.source (eid 0 0)) (.source (eid 1 1)) :=
  .trans (.single (.inl (show Tma.ProgramOrder candidate.view (.source (eid 0 0)) (.source (eid 0 1)) from by change Hopper.ProgramOrder candidate.view (eid 0 0) (eid 0 1); decide)))
    (.single (.inr (.inl (show Tma.CTAControl candidate.view (.source (eid 0 1)) (.source (eid 1 1)) from by change Hopper.CTAControl candidate.view (eid 0 1) (eid 1 1); decide))))
theorem every_resource_family_rejected (histories : Location → List Tma.Entry) :
    ¬Unified.ControlAdmitted HopperStage.block candidate histories :=
  Unified.acyclic_rejects_native_cta_cycle peer_return_before_native actual_same_warp_sync (actual_back_path histories)

end
end Ptx.HopperCollectiveCycleTests
