import Ptx.Kernels.HopperStageOutput
import Ptx.Hopper.UnifiedSchedules

/-! Full aligned collective schedule of every actual stage source thread.
Leader-specific TMA work and differing query/serial numbers are retained in
the source traces but do not change the common native collective sequence. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def stageSchedule : List Wgmma.SourceSignature := [
  ⟨28,⟨28,0,0⟩,.fence⟩,
  ⟨29,⟨29,1,0⟩,.mma 0 0 ["%d0","%d1","%d2","%d3"] 68720001025 68720001153 true⟩,
  ⟨30,⟨30,2,0⟩,.commit 0⟩,
  ⟨31,⟨31,3,0⟩,.wait 1 0⟩]
theorem actual_trace_schedule (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    (trace a b lane).nativeSchedule = stageSchedule := by
  have hg : Ampere.linearThread (ctx lane)/128 = 0 := by rw [ctx_linear]; exact Nat.div_eq_of_lt lane.isLt
  change Wgmma.eventSchedule (middleEvents a b lane (leader lane)++(nativeEvents a b lane (leader lane)++
    (storeResult a b lane (leader lane)).2)) = stageSchedule
  rw [Wgmma.event_schedule_append,Wgmma.event_schedule_append,actual_store_events]
  cases leader lane <;> simp [Wgmma.eventSchedule,Wgmma.eventSignature,Wgmma.collective,
    middleEvents,nativeEvents,storedEvents,fenceMark,hg,stageSchedule,stageCall,Wgmma.makeCall]
  all_goals rfl
theorem stage_schedules_admitted (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Unified.SchedulesAdmitted block (candidate a b) := by
  apply Unified.schedules_admitted_of_participants
  intro actual ht _ lane
  obtain ⟨original,rfl⟩ := List.mem_ofFn.mp ht
  refine ⟨trace a b lane,List.mem_ofFn.mpr ⟨lane,rfl⟩,rfl,?_,?_⟩
  · change Ampere.linearThread (ctx lane) = 128*(Ampere.linearThread (ctx original)/128)+lane.val
    rw [ctx_linear,ctx_linear,Nat.div_eq_of_lt original.isLt]
    omega
  · simp only [Unified.ThreadTrace.alignedSchedule,actual_trace_schedule]
theorem stage_schedules_replay (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    ∃ located, Wgmma.runLocated (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (count lane) {} =
      .ok ((trace a b lane).final,located) ∧ Wgmma.schedule located = stageSchedule := by
  obtain ⟨located,hr,hs⟩ := Unified.trace_schedule_has_checked_replay (source_produced a b lane)
  exact ⟨located,hr,hs.trans (actual_trace_schedule a b lane)⟩

end
end Ptx.Kernels.HopperStage
