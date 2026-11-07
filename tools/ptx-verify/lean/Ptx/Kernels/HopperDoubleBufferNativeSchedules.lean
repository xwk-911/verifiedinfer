import Ptx.Kernels.HopperDoubleBufferNativeReuse
import Ptx.Hopper.UnifiedControl

/-! The complete repeated source's actual native collective schedule. Leader
prefetch work, native query differences and the omitted final prefetch do not
alter its 128-lane aligned sequence. Memory/native-control admission remains
separate from this participation component. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataTileSchedule (tile : Nat) : List Wgmma.SourceSignature := [
  ⟨76,⟨76,4*tile,0⟩,.fence⟩,
  ⟨77,⟨77,4*tile+1,0⟩,.mma tile tile ["%d0","%d1","%d2","%d3"]
    (aDescriptor (stage tile)) (bDescriptor (stage tile)) true⟩,
  ⟨78,⟨78,4*tile+2,0⟩,.commit tile⟩,
  ⟨79,⟨79,4*tile+3,0⟩,.wait (tile+1) 0⟩]
def dataNativeSchedule : Nat → List Wgmma.SourceSignature
  | 0 => []
  | n+1 => dataNativeSchedule n++dataTileSchedule n

theorem data_prepared_mark (a b tiles tile lane) :
    Wgmma.mark (ctx tiles lane)
      (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane)) = ⟨76,4*tile,0⟩ := by
  have hp : (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane)).base.scalar.core.thread.pc = 76 := by simp [preparedState]
  have hl : Ampere.linearThread (ctx tiles lane)/128 = 0 := by
    change Ampere.linearThread (HopperStage.ctx lane)/128 = 0
    rw [HopperStage.ctx_linear]
    exact Nat.div_eq_of_lt lane.isLt
  simp only [Wgmma.mark,hp,preparedState_syncs,data_checkpoint_syncs,hl]

theorem data_issued_mark (a b tiles tile lane) :
    Wgmma.mark (ctx tiles lane)
      (computeIssued (ctx tiles lane) (dataOracle a b tiles lane)
        (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane))
        (aDescriptor (stage tile)) (bDescriptor (stage tile)) (dataCheckpoint a b tiles lane tile).2) = ⟨78,4*tile+2,0⟩ := by
  have hp : (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane)).base.scalar.core.thread.pc = 76 := by simp [preparedState]
  have hl : Ampere.linearThread (ctx tiles lane)/128 = 0 := by
    change Ampere.linearThread (HopperStage.ctx lane)/128 = 0
    rw [HopperStage.ctx_linear]
    exact Nat.div_eq_of_lt lane.isLt
  simp only [Wgmma.mark,computeIssued,Wgmma.issueState,computeFence,Ampere.advance,Ptx.advance]
  rw [hp,preparedState_syncs,data_checkpoint_syncs,hl]

theorem data_compute_schedule (a b tiles tile lane) :
    Wgmma.eventSchedule (computeEvents (ctx tiles lane) (dataOracle a b tiles lane)
      (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane))
      (aDescriptor (stage tile)) (bDescriptor (stage tile)) (dataCheckpoint a b tiles lane tile).2) = dataTileSchedule tile := by
  have hm := data_mark_value a b tiles tile lane
  change Wgmma.mark (ctx tiles lane) (computeFence _) = _ at hm
  simp only [computeEvents,Wgmma.eventSchedule,List.filterMap_cons,List.filterMap_nil,
    Wgmma.eventSignature,Wgmma.collective,Option.map_some]
  rw [data_prepared_mark,hm,data_issued_mark,data_committed_mark,preparedState_groups,data_checkpoint_groups]
  change ([_,⟨_,_,.mma (dataIterationCall a b tiles tile lane).ordinal (dataIterationCall a b tiles tile lane).group
    (dataIterationCall a b tiles tile lane).d.names (dataIterationCall a b tiles tile lane).a
    (dataIterationCall a b tiles tile lane).b (dataIterationCall a b tiles tile lane).scaleD⟩,_,_] : List Wgmma.SourceSignature) = _
  rw [data_call_ordinal,data_call_group,data_call_a,data_call_b]
  rfl

theorem data_prelude_schedule (context oracle s tile tiles leader mapA mapB) :
    Wgmma.eventSchedule (preludeEvents context oracle s tile tiles leader mapA mapB) = [] := by
  unfold preludeEvents
  split_ifs <;> rfl

theorem data_iteration_schedule (a b tiles tile lane) :
    Wgmma.eventSchedule (dataIterationEvents a b tiles tile lane) = dataTileSchedule tile := by
  simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,
    Wgmma.event_schedule_append,data_prelude_schedule,data_compute_schedule,List.nil_append]
  change []++(dataTileSchedule tile++[]) = dataTileSchedule tile
  simp

theorem data_initial_schedule (a b tiles lane) : Wgmma.eventSchedule (dataInitialEvents a b tiles lane) = [] := by
  cases hl : HopperStage.leader lane <;> simp only [dataInitialEvents,hl] <;> rfl

theorem data_initialization_schedule (leader : Bool) : Wgmma.eventSchedule (initializationEvents leader) = [] := by
  cases leader <;> rfl

theorem data_output_schedule (context s lane leader values) :
    Wgmma.eventSchedule (outputEvents context s lane leader values) = [] := by
  cases leader <;> rfl

theorem data_loop_schedule (a b tiles lane n) : Wgmma.eventSchedule (dataLoopEvents a b tiles lane n) = dataNativeSchedule n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : dataLoopEvents a b tiles lane (n+1) = dataLoopEvents a b tiles lane n++dataIterationEvents a b tiles n lane := by
      simp only [dataLoopEvents,loopEvents,dataIterationEvents,dataCheckpoint,Nat.zero_add,zeroRetries]
    rw [he,Wgmma.event_schedule_append,ih,data_iteration_schedule]
    rfl

theorem data_pre_output_schedule (a b tiles lane) :
    Wgmma.eventSchedule (dataPreOutputEvents a b tiles lane) = dataNativeSchedule tiles := by
  by_cases hz : tiles = 0
  · subst tiles
    exact data_initialization_schedule _
  · simp only [dataPreOutputEvents,hz,ite_false,dataKernelLoopEvents]
    change Wgmma.eventSchedule (dataInitialEvents a b tiles lane++dataLoopEvents a b tiles lane tiles) = _
    rw [Wgmma.event_schedule_append,data_initial_schedule,data_loop_schedule,List.nil_append]

theorem data_complete_native_schedule (a b tiles lane) :
    (dataCompleteTrace a b tiles lane).nativeSchedule = dataNativeSchedule tiles := by
  change Wgmma.eventSchedule (dataPreOutputEvents a b tiles lane++_) = _
  rw [Wgmma.event_schedule_append,data_pre_output_schedule,data_output_schedule,List.append_nil]

theorem data_native_schedules_admitted (a b tiles) :
    Unified.SchedulesAdmitted HopperStage.block (dataCompleteCandidate a b tiles) := by
  apply Unified.schedules_admitted_of_participants
  intro actual ht _ lane
  obtain ⟨original,rfl⟩ := List.mem_ofFn.mp ht
  refine ⟨dataCompleteTrace a b tiles lane,List.mem_ofFn.mpr ⟨lane,rfl⟩,rfl,?_,?_⟩
  · change Ampere.linearThread (HopperStage.ctx lane) = 128*(Ampere.linearThread (HopperStage.ctx original)/128)+lane.val
    rw [HopperStage.ctx_linear,HopperStage.ctx_linear,Nat.div_eq_of_lt original.isLt]
    omega
  · simp only [Unified.ThreadTrace.alignedSchedule,data_complete_native_schedule]

theorem data_native_schedules_replay (a b tiles lane) (hb : tiles ≤ 2^28) :
    ∃ located, Wgmma.runLocated (ctx tiles lane) (dataOracle a b tiles lane) code (completeSteps tiles lane) {} =
      .ok ((dataCompleteTrace a b tiles lane).final,located) ∧ Wgmma.schedule located = dataNativeSchedule tiles := by
  obtain ⟨located,hr,hs⟩ := Unified.trace_schedule_has_checked_replay (data_source_produced a b tiles lane hb)
  exact ⟨located,hr,hs.trans (data_complete_native_schedule a b tiles lane)⟩

end
end Ptx.Kernels.HopperDoubleBuffer
