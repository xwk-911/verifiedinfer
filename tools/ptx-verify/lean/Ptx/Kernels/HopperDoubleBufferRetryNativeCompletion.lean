import Ptx.Kernels.HopperDoubleBufferRetryNativePublication

/-! Actual native wait-group identities and completion for arbitrary retries.
No completed-reply or eventual-readiness premise replaces the actual source
wait. Global native control/RF/reuse and full arithmetic admission are separate. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def replyNativeWaitId (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) (tile : Nat) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,replyTileStart tiles lane reply retries tile+retries tile+preludeEventCount tile tiles (HopperStage.leader lane)+4⟩
def ReplySourceFamily.nativeWaitId {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) : Ptx.Event.EventId :=
  replyNativeWaitId tiles lane (family.replies lane) (family.schedules lane) tile

theorem reply_checkpoint_groups (tiles lane reply retries tile) :
    (replyTileCheckpoint tiles lane reply retries tile).1.ledger.groups = tile := by simp [replyTileCheckpoint,initialLoopState]

theorem reply_checkpoint_completed_le (tiles lane reply retries tile) (hb : tiles ≤ 2^28) (ht : tile < tiles) :
    (replyTileCheckpoint tiles lane reply retries tile).1.ledger.completed ≤ tile := by
  have hh := (loopCheckpoint_ready (ctx tiles lane) reply 0 tiles (HopperStage.leader lane) retries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
    rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _)
    (by omega) tile (by omega)).2.2.2.1
  change (replyTileCheckpoint tiles lane reply retries tile).1.ledger.completed ≤
    (replyTileCheckpoint tiles lane reply retries tile).1.ledger.groups at hh
  rwa [reply_checkpoint_groups] at hh

theorem reply_committed_mark (tiles lane reply retries tile) :
    Wgmma.mark (ctx tiles lane) (computeCommitted (ctx tiles lane) reply
      (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile) (HopperStage.leader lane))
      (aDescriptor (stage tile)) (bDescriptor (stage tile)) (replyTileCheckpoint tiles lane reply retries tile).2) = ⟨79,4*tile+3,0⟩ := by
  have hp : (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile)
      (HopperStage.leader lane)).base.scalar.core.thread.pc = 76 := by simp [preparedState]
  have hl : Ampere.linearThread (ctx tiles lane)/128 = 0 := by
    change Ampere.linearThread (HopperStage.ctx lane)/128 = 0
    rw [HopperStage.ctx_linear]
    exact Nat.div_eq_of_lt lane.isLt
  have hs : (replyTileCheckpoint tiles lane reply retries tile).1.ledger.syncs = 4*tile := by
    simp [replyTileCheckpoint,loopCheckpoint_syncs,initialLoopState]
  simp only [Wgmma.mark,computeCommitted,computeIssued,Wgmma.issueState,computeFence,Ampere.advance,Ptx.advance]
  rw [hp,preparedState_syncs,hs,hl]

theorem reply_compute_completed (tiles lane reply retries tile) (hb : tiles ≤ 2^28) (ht : tile < tiles) :
    (computeState (ctx tiles lane) reply
      (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile) (HopperStage.leader lane))
      (aDescriptor (stage tile)) (bDescriptor (stage tile)) (replyTileCheckpoint tiles lane reply retries tile).2).ledger.completed = tile+1 := by
  rw [computeState_completed,preparedState_groups,reply_checkpoint_groups]
  simpa only [preparedState_completed,preparedState_groups,reply_checkpoint_groups] using reply_checkpoint_completed_le tiles lane reply retries tile hb ht

theorem reply_iteration_native_wait_at (tiles lane reply retries tile) (hb : tiles ≤ 2^28) (ht : tile < tiles) :
    (replyIterationEvents tiles lane reply retries tile)[retries tile+preludeEventCount tile tiles (HopperStage.leader lane)+4]? =
      some (.wait ⟨79,4*tile+3,0⟩ (tile+1) 0 (replyTileCheckpoint tiles lane reply retries tile).1.ledger.completed (tile+1)
        ((preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile) (HopperStage.leader lane)).base.scalar.core.queries+1)) := by
  simp only [replyIterationEvents,iterationEvents,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
  simp only [List.length_replicate]
  rw [List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by rw [prelude_events_length]; omega),prelude_events_length]
  rw [show retries tile+preludeEventCount tile tiles (HopperStage.leader lane)+4-retries tile-1-
    preludeEventCount tile tiles (HopperStage.leader lane) = 3 by omega]
  change some (Wgmma.Event.wait _ _ _ _ _ _) = _
  rw [reply_committed_mark,preparedState_groups,reply_checkpoint_groups,preparedState_completed,reply_compute_completed tiles lane reply retries tile hb ht]

theorem reply_complete_native_wait_at (tiles lane reply retries tile) (hb : tiles ≤ 2^28) (ht : tile < tiles) :
    (replyPositiveEvents tiles lane reply retries)[(replyNativeWaitId tiles lane reply retries tile).serial]? =
      some (.wait ⟨79,4*tile+3,0⟩ (tile+1) 0 (replyTileCheckpoint tiles lane reply retries tile).1.ledger.completed (tile+1)
        ((preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile) (HopperStage.leader lane)).base.scalar.core.queries+1)) := by
  have hh := reply_complete_iteration_at tiles lane reply retries tile _ _ ht (reply_iteration_native_wait_at tiles lane reply retries tile hb ht)
  simpa only [replyNativeWaitId,Nat.add_assoc] using hh

theorem family_native_wait_at {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hb : tiles ≤ 2^28) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) :
    candidate.eventAt (family.nativeWaitId tile lane) =
      some (.wait ⟨79,4*tile+3,0⟩ (tile+1) 0 (replyTileCheckpoint tiles lane (family.replies lane) (family.schedules lane) tile).1.ledger.completed (tile+1)
        ((preparedState (replyTileCheckpoint tiles lane (family.replies lane) (family.schedules lane) tile).1 tile tiles (family.schedules lane tile)
          (HopperStage.leader lane)).base.scalar.core.queries+1)) :=
  family_event_at family hw lane _ _ (reply_complete_native_wait_at tiles lane (family.replies lane) (family.schedules lane) tile hb ht)

theorem retry_native_completed {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hb : tiles ≤ 2^28) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) :
    Unified.WgmmaCompletedAt candidate (family.mmaId tile 0) (family.nativeWaitId tile lane) := by
  refine ⟨familyCollective family hw tile ht,lane,⟨79,4*tile+3,0⟩,tile+1,0,
    (replyTileCheckpoint tiles lane (family.replies lane) (family.schedules lane) tile).1.ledger.completed,tile+1,_,
    family_native_wait_at family hw hb tile ht lane,rfl,?_,?_,?_,?_,?_,by omega,by decide⟩
  · change (replyMmaId tiles lane (family.replies lane) (family.schedules lane) tile).serial <
      (replyNativeWaitId tiles lane (family.replies lane) (family.schedules lane) tile).serial
    simp only [replyMmaId,replyNativeWaitId]
    omega
  · change 0 = (replyMark tiles lane (family.replies lane) (family.schedules lane) tile).warpgroup
    rw [reply_mark_value]
  · change (replyMark tiles lane (family.replies lane) (family.schedules lane) tile).sequence < 4*tile+3
    rw [reply_mark_value]
    change 4*tile+1 < 4*tile+3
    omega
  · change (replyCall tiles lane (family.replies lane) (family.schedules lane) tile).group < tile+1
    rw [reply_call_group]
    omega
  · have hc := reply_checkpoint_completed_le tiles lane (family.replies lane) (family.schedules lane) tile hb ht
    omega

theorem retry_native_completed_order {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hb : tiles ≤ 2^28) (tile : Nat) (ht : tile < tiles)
    (lane : Wgmma.Lane) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate (retryHistories family) dataCluster
      (retryNativeLocation family tile operand) (retryNativeRead family tile operand) (.base (.tma (.source (family.nativeWaitId tile lane)))) :=
  Unified.native_completed_byte_order ⟨retry_native_completed family hw hb tile ht lane,
    family.marks tile 0,family.calls tile 0,Unified.collective_representative (familyCollective family hw tile ht),rfl⟩

end
end Ptx.Kernels.HopperDoubleBuffer
