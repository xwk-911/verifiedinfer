import Ptx.Kernels.HopperDoubleBufferNativePublication
import Ptx.Hopper.UnifiedOrderSafety

/-! Source-indexed wait_group 0 completion for every actual tile/lane. This
uses the native ledger and matched collective; a CTA rendezvous alone does
not complete an asynchronous operand read. Full memory admission is separate. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataNativeWaitId (a : TileA) (b : TileB) (tiles tile : Nat) (lane : Wgmma.Lane) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,dataTileStart a b tiles tile lane+(dataPreludeLength tiles tile lane+4)⟩
def dataNativeWaitMark (tile : Nat) : Wgmma.Mark := ⟨79,4*tile+3,0⟩

theorem data_checkpoint_groups (a b tiles lane tile) : (dataCheckpoint a b tiles lane tile).1.ledger.groups = tile := by
  simp [dataCheckpoint,initialLoopState]

theorem data_checkpoint_completed_le (a b tiles lane tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    (dataCheckpoint a b tiles lane tile).1.ledger.completed ≤ tile := by
  have hc := (data_loop_ready a b tiles lane tile (by omega) hb (by omega)).2.2.2.1
  rwa [data_checkpoint_groups] at hc

theorem data_committed_mark (a b tiles tile lane) :
    Wgmma.mark (ctx tiles lane)
      (computeCommitted (ctx tiles lane) (dataOracle a b tiles lane)
        (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane))
        (aDescriptor (stage tile)) (bDescriptor (stage tile)) (dataCheckpoint a b tiles lane tile).2) = dataNativeWaitMark tile := by
  have hp : (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane)).base.scalar.core.thread.pc = 76 := by
    simp [preparedState]
  have hl : Ampere.linearThread (ctx tiles lane)/128 = 0 := by
    change Ampere.linearThread (HopperStage.ctx lane)/128 = 0
    rw [HopperStage.ctx_linear]
    exact Nat.div_eq_of_lt lane.isLt
  simp only [Wgmma.mark,computeCommitted,computeIssued,Wgmma.issueState,computeFence,Ampere.advance,Ptx.advance]
  rw [hp,preparedState_syncs,data_checkpoint_syncs,hl]
  rfl

theorem data_compute_completed (a b tiles tile lane) (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    (computeState (ctx tiles lane) (dataOracle a b tiles lane)
      (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane))
      (aDescriptor (stage tile)) (bDescriptor (stage tile)) (dataCheckpoint a b tiles lane tile).2).ledger.completed = tile+1 := by
  rw [computeState_completed,preparedState_groups,data_checkpoint_groups]
  simpa only [preparedState_completed,preparedState_groups,data_checkpoint_groups] using
    data_checkpoint_completed_le a b tiles lane tile ht hb

theorem data_iteration_native_wait_at (a b tiles tile lane) (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    (dataIterationEvents a b tiles tile lane)[dataPreludeLength tiles tile lane+4]? =
      some (.wait (dataNativeWaitMark tile) (tile+1) 0
        (dataCheckpoint a b tiles lane tile).1.ledger.completed (tile+1) (nativeQuery tiles tile (HopperStage.leader lane)+1)) := by
  simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,List.append_assoc]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by rw [data_prelude_length]; omega),data_prelude_length]
  have he : dataPreludeLength tiles tile lane+4-1-dataPreludeLength tiles tile lane = 3 := by omega
  rw [he]
  change some (Wgmma.Event.wait _ _ _ _ _ _) = _
  rw [data_committed_mark,preparedState_groups,data_checkpoint_groups,preparedState_completed,
    data_compute_completed a b tiles tile lane ht hb,data_prepared_native_query a b tiles lane tile ht]

theorem data_source_native_wait (a b tiles tile lane) (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    (dataCompleteCandidate a b tiles).eventAt (dataNativeWaitId a b tiles tile lane) =
      some (.wait (dataNativeWaitMark tile) (tile+1) 0
        (dataCheckpoint a b tiles lane tile).1.ledger.completed (tile+1) (nativeQuery tiles tile (HopperStage.leader lane)+1)) := by
  change (dataCompleteCandidate a b tiles).eventAt ⟨(dataCompleteTrace a b tiles lane).id,_⟩ = _
  rw [Unified.eventAt_of_member (data_source_ids_unique a b tiles) (List.mem_ofFn.mpr ⟨lane,rfl⟩)]
  exact data_complete_iteration_at a b tiles tile lane ht _ _ (data_iteration_native_wait_at a b tiles tile lane ht hb)

theorem data_native_completed (a b tiles tile lane) (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    Unified.WgmmaCompletedAt (dataCompleteCandidate a b tiles) (dataMmaId a b tiles tile 0) (dataNativeWaitId a b tiles tile lane) := by
  refine ⟨dataCollective a b tiles tile ht,lane,dataNativeWaitMark tile,tile+1,0,
    (dataCheckpoint a b tiles lane tile).1.ledger.completed,tile+1,nativeQuery tiles tile (HopperStage.leader lane)+1,
    data_source_native_wait a b tiles tile lane ht hb,rfl,?_,?_,?_,?_,?_,by omega,by decide⟩
  · change dataMmaIndex a b tiles tile lane < dataTileStart a b tiles tile lane+(dataPreludeLength tiles tile lane+4)
    unfold dataMmaIndex
    omega
  · change 0 = (dataIterationMark a b tiles tile lane).warpgroup
    rw [data_mark_value]
  · change (dataIterationMark a b tiles tile lane).sequence < 4*tile+3
    rw [data_mark_value]
    change 4*tile+1 < 4*tile+3
    omega
  · change (dataIterationCall a b tiles tile lane).group < tile+1
    rw [data_call_group]
    omega
  · have hc := data_checkpoint_completed_le a b tiles lane tile ht hb
    omega

theorem data_native_completed_order (a b tiles tile lane) (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster (dataNativeLocation a b tiles tile operand)
      (dataNativeRead a b tiles tile operand) (.base (.tma (.source (dataNativeWaitId a b tiles tile lane)))) :=
  Unified.native_completed_byte_order ⟨data_native_completed a b tiles tile lane ht hb,
    ⟨77,4*tile+1,0⟩,dataIterationCall a b tiles tile 0,data_collective_representative a b tiles tile ht,rfl⟩

end
end Ptx.Kernels.HopperDoubleBuffer
