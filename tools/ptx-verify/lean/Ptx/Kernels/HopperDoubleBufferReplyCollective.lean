import Ptx.Kernels.HopperDoubleBufferReplyIndices
import Ptx.Kernels.HopperDoubleBufferDataCollective

/-! Collective call/mark shape independent of each lane's oracle and failed
wait schedule. Captured input/output/operand values are preserved, not proved
correct or uniform. Only the source collective shape is established here. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem reply_call_a (tiles lane reply retries tile) :
    (replyCall tiles lane reply retries tile).a = aDescriptor (stage tile) := wrapped_a_descriptor _
theorem reply_call_b (tiles lane reply retries tile) :
    (replyCall tiles lane reply retries tile).b = bDescriptor (stage tile) := wrapped_b_descriptor _
theorem reply_call_lane (tiles lane reply retries tile) : (replyCall tiles lane reply retries tile).lane = lane := by
  apply Fin.ext
  change Ampere.linearThread (ctx tiles lane)%128 = lane.val
  change Ampere.linearThread (HopperStage.ctx lane)%128 = lane.val
  rw [HopperStage.ctx_linear,Nat.mod_eq_of_lt lane.isLt]
theorem reply_call_group (tiles lane reply retries tile) : (replyCall tiles lane reply retries tile).group = tile := by
  change (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile) (HopperStage.leader lane)).ledger.groups = tile
  simp [replyTileCheckpoint,initialLoopState]
theorem reply_call_ordinal (tiles lane reply retries tile) : (replyCall tiles lane reply retries tile).ordinal = tile := by
  have he : (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile)
      (HopperStage.leader lane)).ledger.calls = (replyTileCheckpoint tiles lane reply retries tile).1.ledger.calls :=
    congrArg (fun x => x.2.2.1) (preparedState_bookkeeping
      (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile) (HopperStage.leader lane))
  change (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile) (HopperStage.leader lane)).ledger.calls.length = tile
  rw [he]
  dsimp only [replyTileCheckpoint]
  rw [loopCheckpoint_call_count]
  change 0+tile = tile
  exact Nat.zero_add tile

theorem reply_mark_value (tiles lane reply retries tile) : replyMark tiles lane reply retries tile = ⟨77,4*tile+1,0⟩ := by
  have hpc : (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile)
      (HopperStage.leader lane)).base.scalar.core.thread.pc = 76 := by simp [preparedState]
  have hl : Ampere.linearThread (ctx tiles lane)/128 = 0 := by
    change Ampere.linearThread (HopperStage.ctx lane)/128 = 0
    rw [HopperStage.ctx_linear]
    exact Nat.div_eq_of_lt lane.isLt
  have hs : (replyTileCheckpoint tiles lane reply retries tile).1.ledger.syncs = 4*tile := by
    simp only [replyTileCheckpoint,loopCheckpoint_syncs]
    simp [initialLoopState]
  simp only [replyMark,Wgmma.mark,computeFence,Ampere.advance,Ptx.advance]
  rw [hpc,preparedState_syncs,hs,hl]

theorem reply_calls_cohort (tiles tile) (replies : Wgmma.Lane → Wgmma.Oracle) (schedules : Wgmma.Lane → Nat → Nat) :
    Wgmma.Cohort (fun lane => replyCall tiles lane (replies lane) (schedules lane) tile) := by
  constructor
  · intro lane
    exact reply_call_lane tiles lane (replies lane) (schedules lane) tile
  · intro lane
    rw [reply_call_a,reply_call_a]
  · intro lane
    rw [reply_call_b,reply_call_b]
  · intro lane
    change ["%d0","%d1","%d2","%d3"] = ["%d0","%d1","%d2","%d3"]
    rfl
  · intro lane
    rw [reply_call_ordinal,reply_call_ordinal]
  · intro lane
    rw [reply_call_group,reply_call_group]

end
end Ptx.Kernels.HopperDoubleBuffer
