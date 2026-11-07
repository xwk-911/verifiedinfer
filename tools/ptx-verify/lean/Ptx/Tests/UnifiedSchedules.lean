import Ptx.Kernels.HopperStageInputs

/-! A complete 128-thread source execution can still violate aligned
collectives: only tid.x=0 threads commit an empty WGMMA group. There are no
pending matrix operations, yet the collective schedule must reject it.
This small handwritten AST is a semantic litmus, not a generated/GPU fixture.
-/
namespace Ptx.UnifiedScheduleTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def code : List Hopper.Instr := [
  .ampere (.scalar (.integer (.setp .eq "%p" .tid (.imm 0)))),
  .ampere (.scalar (.integer (.branch "%p" false 3))),
  .wgmma .commit,.ampere (.scalar (.integer .ret))]
def oracle : Wgmma.Oracle := {base := {ampere := {scalar := fun _ => .integer 0,bytes := fun _ => []},wait := fun _ => false}}
def count (lane : Wgmma.Lane) : Nat := if (HopperStage.tid lane).x = 0 then 4 else 3
def result (lane : Wgmma.Lane) : Wgmma.State × List Wgmma.Event :=
  (Wgmma.run (HopperStage.ctx lane) oracle code (count lane) {}).toOption.getD ({},[])
def trace (lane : Wgmma.Lane) : Unified.ThreadTrace := ⟨(HopperStage.ctx lane).id,oracle,count lane,(result lane).1,(result lane).2⟩
def candidate : Unified.Candidate := ⟨List.ofFn trace⟩
def launch : Scalar.Launch := HopperStage.launch (fun _ => .bits (byte 0))

theorem all_runs_succeed : ∀ lane : Wgmma.Lane,
    (Wgmma.run (HopperStage.ctx lane) oracle code (count lane) {}).toOption.isSome = true := by decide
theorem all_complete_metadata : ∀ lane : Wgmma.Lane,
    (((result lane).1.base.scalar.core.thread.status == .done) &&
      ((Wgmma.pending (result lane).1.ledger).length == 0)) = true := by decide
theorem actual_run (lane : Wgmma.Lane) :
    Wgmma.run (HopperStage.ctx lane) oracle code (count lane) {} = .ok (result lane) := by
  cases hs : Wgmma.run (HopperStage.ctx lane) oracle code (count lane) {} with
  | error fault => have hh := all_runs_succeed lane; rw [hs] at hh; cases hh
  | ok value => simp only [result,hs,Except.toOption,Option.getD_some]
theorem source_produced (lane : Wgmma.Lane) : Unified.Produced code HopperStage.params HopperStage.block (trace lane) := actual_run lane
theorem source_complete : Unified.Complete candidate := by
  intro actual ht
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  exact Wgmma.complete_of_metadata _ (all_complete_metadata lane)
theorem trace_ids_unique : (candidate.traces.map Unified.ThreadTrace.id).Nodup := by
  simpa only [candidate,List.map_ofFn,Function.comp_def,trace] using
    (show (List.ofFn (fun lane : Wgmma.Lane => (HopperStage.ctx lane).id)).Nodup from by decide)
theorem source_well_formed : Unified.WellFormed code launch candidate := by
  refine ⟨?_,trace_ids_unique,?_,?_⟩
  · simp [launch,HopperStage.launch,HopperStage.geometry,HopperStage.block,Geometry.Valid,Dim3.Positive,Dim3.one]
  · intro actual ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨HopperStage.ctx_valid lane,source_produced lane⟩
  · intro id hi
    obtain ⟨lane,he⟩ := HopperStage.ctx_covered hi
    exact ⟨trace lane,List.mem_ofFn.mpr ⟨lane,rfl⟩,he⟩
theorem empty_commit_schedule_diverges :
    (trace 0).nativeSchedule = [⟨2,⟨2,0,0⟩,.commit 0⟩] ∧ (trace 1).nativeSchedule = [] := by decide
theorem divergent_empty_commit_rejected : ¬Unified.SchedulesAdmitted HopperStage.block candidate := by decide
theorem ordinary_only_schedule_accepted :
    Unified.SchedulesAdmitted .one ⟨[{trace 0 with events := []}]⟩ := by decide

-- Metadata-only fixtures; no source or tensor admission is asserted for them.
def scaleCall (lane : Wgmma.Lane) (scale : Bool) : Wgmma.Call := {
  ordinal := 0
  group := 0
  lane := lane
  d := ⟨"d0","d1","d2","d3"⟩
  a := Wgmma.packedA
  b := Wgmma.packedB
  scaleD := scale
  input := fun _ => 0
  output := fun _ => 0
  query := 0
}
def scaleTrace (lane : Wgmma.Lane) (scale : Bool) : Unified.ThreadTrace :=
  {trace lane with events := [.mma ⟨2,0,0⟩ (scaleCall lane scale)]}
theorem per_lane_scale_retained : (scaleTrace 0 true).nativeSchedule ≠ (scaleTrace 1 false).nativeSchedule := by decide
theorem per_lane_scale_not_collective_uniformity :
    Unified.participantMatches HopperStage.block (scaleTrace 0 true) (scaleTrace 1 false) 1 = true := by decide

end
end Ptx.UnifiedScheduleTests
