import Ptx.Kernels.HopperDoubleBufferRetryNativeCompletion
import Ptx.Kernels.HopperDoubleBufferNativeSchedules

/-! Actual aligned native participation with arbitrary finite per-lane/tile
failed waits. Retry and prefetch work preserve the fixed native sequence;
source coverage supplies all 128 actual lanes. This participation component
does not establish combined control acyclicity or memory admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem reply_prepared_mark (tiles lane reply retries tile) :
    Wgmma.mark (ctx tiles lane)
      (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile) (HopperStage.leader lane)) =
        ⟨76,4*tile,0⟩ := by
  have hp : (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile)
      (HopperStage.leader lane)).base.scalar.core.thread.pc = 76 := by simp [preparedState]
  have hl : Ampere.linearThread (ctx tiles lane)/128 = 0 := by
    change Ampere.linearThread (HopperStage.ctx lane)/128 = 0
    rw [HopperStage.ctx_linear]
    exact Nat.div_eq_of_lt lane.isLt
  have hs : (replyTileCheckpoint tiles lane reply retries tile).1.ledger.syncs = 4*tile := by
    simp [replyTileCheckpoint,loopCheckpoint_syncs,initialLoopState]
  simp only [Wgmma.mark,hp,preparedState_syncs,hs,hl]

theorem reply_issued_mark (tiles lane reply retries tile) :
    Wgmma.mark (ctx tiles lane) (computeIssued (ctx tiles lane) reply
      (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile) (HopperStage.leader lane))
      (aDescriptor (stage tile)) (bDescriptor (stage tile)) (replyTileCheckpoint tiles lane reply retries tile).2) =
        ⟨78,4*tile+2,0⟩ := by
  have hp : (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile)
      (HopperStage.leader lane)).base.scalar.core.thread.pc = 76 := by simp [preparedState]
  have hl : Ampere.linearThread (ctx tiles lane)/128 = 0 := by
    change Ampere.linearThread (HopperStage.ctx lane)/128 = 0
    rw [HopperStage.ctx_linear]
    exact Nat.div_eq_of_lt lane.isLt
  have hs : (replyTileCheckpoint tiles lane reply retries tile).1.ledger.syncs = 4*tile := by
    simp [replyTileCheckpoint,loopCheckpoint_syncs,initialLoopState]
  simp only [Wgmma.mark,computeIssued,Wgmma.issueState,computeFence,Ampere.advance,Ptx.advance]
  rw [hp,preparedState_syncs,hs,hl]

theorem reply_compute_schedule (tiles lane reply retries tile) :
    Wgmma.eventSchedule (computeEvents (ctx tiles lane) reply
      (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile) (HopperStage.leader lane))
      (aDescriptor (stage tile)) (bDescriptor (stage tile)) (replyTileCheckpoint tiles lane reply retries tile).2) = dataTileSchedule tile := by
  have hm := reply_mark_value tiles lane reply retries tile
  change Wgmma.mark (ctx tiles lane) (computeFence _) = _ at hm
  simp only [computeEvents,Wgmma.eventSchedule,List.filterMap_cons,List.filterMap_nil,
    Wgmma.eventSignature,Wgmma.collective,Option.map_some]
  rw [reply_prepared_mark,hm,reply_issued_mark,reply_committed_mark,preparedState_groups,reply_checkpoint_groups]
  change ([_,⟨_,_,.mma (replyCall tiles lane reply retries tile).ordinal (replyCall tiles lane reply retries tile).group
    (replyCall tiles lane reply retries tile).d.names (replyCall tiles lane reply retries tile).a
    (replyCall tiles lane reply retries tile).b (replyCall tiles lane reply retries tile).scaleD⟩,_,_] : List Wgmma.SourceSignature) = _
  rw [reply_call_ordinal,reply_call_group,reply_call_a,reply_call_b]
  rfl

theorem wait_replicate_native_schedule (context bar parity retries answer) :
    Wgmma.eventSchedule (List.replicate retries (waitEvent context bar parity answer)) = [] := by
  induction retries with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,Wgmma.eventSchedule,List.filterMap_cons,Wgmma.eventSignature,waitEvent,Wgmma.collective,Option.map_none] using ih

theorem reply_iteration_native_schedule (tiles lane reply retries tile) :
    Wgmma.eventSchedule (replyIterationEvents tiles lane reply retries tile) = dataTileSchedule tile := by
  simp only [replyIterationEvents,iterationEvents,Wgmma.event_schedule_append,wait_replicate_native_schedule,
    data_prelude_schedule,reply_compute_schedule,List.nil_append]
  change []++(dataTileSchedule tile++[]) = dataTileSchedule tile
  simp

theorem reply_initial_native_schedule (lane reply) : Wgmma.eventSchedule (replyInitialEvents lane reply) = [] := by
  cases hl : HopperStage.leader lane <;> simp only [replyInitialEvents,hl] <;> rfl

theorem reply_loop_native_schedule (tiles lane reply retries n) :
    Wgmma.eventSchedule (replyLoopEvents tiles lane reply retries n) = dataNativeSchedule n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : replyLoopEvents tiles lane reply retries (n+1) =
        replyLoopEvents tiles lane reply retries n++replyIterationEvents tiles lane reply retries n := by
      simp only [replyLoopEvents,loopEvents,replyIterationEvents,replyTileCheckpoint,Nat.zero_add]
    rw [he,Wgmma.event_schedule_append,ih,reply_iteration_native_schedule]
    rfl

theorem reply_complete_native_schedule (tiles lane reply retries) :
    Wgmma.eventSchedule (replyPositiveEvents tiles lane reply retries) = dataNativeSchedule tiles := by
  simp only [replyPositiveEvents,← List.append_assoc]
  change Wgmma.eventSchedule ((replyInitialEvents lane reply++replyLoopEvents tiles lane reply retries tiles)++_) = _
  rw [Wgmma.event_schedule_append,Wgmma.event_schedule_append,reply_initial_native_schedule,
    reply_loop_native_schedule,data_output_schedule,List.nil_append,List.append_nil]

theorem retry_trace_family {tiles initial candidate trace} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (ht : trace ∈ candidate.traces) :
    ∃ lane, trace = family.traces lane := by
  obtain ⟨lane,hlane⟩ := HopperStage.ctx_covered (hw.2.2.1 trace ht).1
  change (ctx tiles lane).id = trace.id at hlane
  exact ⟨lane,Unified.unique_trace_id hw.2.1 ht (family.members lane) (hlane.symm.trans (family.ids lane).symm)⟩

theorem retry_family_native_schedule {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) :
    (family.traces lane).nativeSchedule = dataNativeSchedule tiles := by
  rw [Unified.ThreadTrace.nativeSchedule,family.events,reply_complete_native_schedule]

theorem retry_native_schedules_admitted {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) :
    Unified.SchedulesAdmitted HopperStage.block candidate := by
  apply Unified.schedules_admitted_of_participants
  intro actual ht _ lane
  obtain ⟨original,rfl⟩ := retry_trace_family family hw ht
  refine ⟨family.traces lane,family.members lane,?_,?_,?_⟩
  · rw [family.ids,family.ids]; rfl
  · change (family.traces lane).id.tid.linear HopperStage.block = 128*((family.traces original).id.tid.linear HopperStage.block/128)+lane.val
    rw [family.ids,family.ids]
    change Ampere.linearThread (HopperStage.ctx lane) = 128*(Ampere.linearThread (HopperStage.ctx original)/128)+lane.val
    rw [HopperStage.ctx_linear,HopperStage.ctx_linear,Nat.div_eq_of_lt original.isLt]
    omega
  · simp only [Unified.ThreadTrace.alignedSchedule,retry_family_native_schedule]

theorem completed_positive_native_schedules_admitted {tiles initial candidate} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate) :
    Unified.SchedulesAdmitted HopperStage.block candidate := by
  obtain ⟨family⟩ := completed_candidate_reply_family ht hb hw hc
  exact retry_native_schedules_admitted family hw

theorem zero_complete_native_schedule (lane : Wgmma.Lane) : Wgmma.eventSchedule (completeEvents 0 lane) = [] := by
  simp only [completeEvents,Wgmma.event_schedule_append,preOutputEvents,ite_true,
    data_initialization_schedule,data_output_schedule,List.nil_append]

theorem completed_candidate_native_schedules_admitted {tiles initial candidate} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate) :
    Unified.SchedulesAdmitted HopperStage.block candidate := by
  by_cases hz : tiles = 0
  · subst tiles
    apply Unified.schedules_admitted_of_participants
    intro trace ht hn lane
    obtain ⟨original,_,hzero | hpositive⟩ := completed_candidate_trace_reconstruct (by decide) hw hc ht
    · have he : trace.nativeSchedule = [] := by
        rw [Unified.ThreadTrace.nativeSchedule,hzero.2.2.2,zero_complete_native_schedule]
      exact (hn he).elim
    · have hh := hpositive.1
      omega
  · exact completed_positive_native_schedules_admitted (by omega) hb hw hc

end
end Ptx.Kernels.HopperDoubleBuffer
