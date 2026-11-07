import Ptx.Kernels.HopperDoubleBufferEventIndices
import Ptx.Kernels.HopperDoubleBufferDataTensor

/-! Every actual tile has a source-indexed 128-lane collective. Matching
marks and tensor arithmetic are components, not full native-control, shared
memory or resource admission of the complete launch. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem preparedState_syncs (s : Wgmma.State) (tile tiles retries : Nat) (leader : Bool) :
    (preparedState s tile tiles retries leader).ledger.syncs = s.ledger.syncs :=
  congrArg (fun x => x.2.2.2) (preparedState_bookkeeping s tile tiles retries leader)

theorem iterationState_syncs (ctx oracle s tile tiles retries leader values) :
    (iterationState ctx oracle s tile tiles retries leader values).ledger.syncs = s.ledger.syncs+4 := by
  change (computeState ctx oracle (preparedState s tile tiles retries leader)
    (aDescriptor (stage tile)) (bDescriptor (stage tile)) values).ledger.syncs = _
  rw [computeState_syncs,preparedState_syncs]

theorem loopCheckpoint_syncs (ctx oracle first tiles leader retries s values n) :
    (loopCheckpoint ctx oracle first tiles leader retries s values n).1.ledger.syncs = s.ledger.syncs+4*n := by
  induction n with
  | zero => simp [loopCheckpoint]
  | succ n ih =>
    rw [loopCheckpoint,iterationState_syncs,ih]
    omega

theorem data_checkpoint_syncs (a b tiles lane tile) :
    (dataCheckpoint a b tiles lane tile).1.ledger.syncs = 4*tile := by
  simp only [dataCheckpoint,loopCheckpoint_syncs]
  simp [initialLoopState]

theorem data_mark_value (a b tiles tile lane) :
    dataIterationMark a b tiles tile lane = ⟨77,4*tile+1,0⟩ := by
  have hpc : (preparedState (dataCheckpoint a b tiles lane tile).1 tile tiles 0 (HopperStage.leader lane)).base.scalar.core.thread.pc = 76 := by
    simp [preparedState]
  have hl : Ampere.linearThread (ctx tiles lane)/128 = 0 := by
    change Ampere.linearThread (HopperStage.ctx lane)/128 = 0
    rw [HopperStage.ctx_linear]
    exact Nat.div_eq_of_lt lane.isLt
  simp only [dataIterationMark,Wgmma.mark,computeFence,Ampere.advance,Ptx.advance]
  rw [hpc,preparedState_syncs,data_checkpoint_syncs,hl]

theorem data_marks_same (a b tiles tile lane) :
    dataIterationMark a b tiles tile lane = dataIterationMark a b tiles tile 0 := by
  rw [data_mark_value,data_mark_value]

def dataCollective (a : TileA) (b : TileB) (tiles tile : Nat) (ht : tile < tiles) :
    Unified.Collective (dataCompleteCandidate a b tiles) (dataMmaId a b tiles tile 0) := {
  calls := dataIterationCall a b tiles tile
  marks := dataIterationMark a b tiles tile
  sources := dataMmaId a b tiles tile
  representative := rfl
  matched := fun lane => data_candidate_mma_at a b tiles tile lane ht
  sameCTA := fun _ => rfl
  sameMark := data_marks_same a b tiles tile
  cohort := data_calls_cohort a b tiles tile
}

theorem data_collective_representative (a b tiles tile) (ht : tile < tiles) :
    (dataCompleteCandidate a b tiles).representativeAt (dataMmaId a b tiles tile 0) =
      some (⟨77,4*tile+1,0⟩,dataIterationCall a b tiles tile 0) := by
  simpa only [dataCollective,data_mark_value] using Unified.collective_representative (dataCollective a b tiles tile ht)

theorem data_collective_lanes_distinct (a b tiles tile) (ht : tile < tiles) :
    Function.Injective (dataMmaId a b tiles tile) :=
  Unified.collective_member_ids_unique (dataCollective a b tiles tile ht)

theorem data_collective_tiles_distinct (a b tiles) (left right : Nat) (hl : left < tiles) (hr : right < tiles)
    (lane : Wgmma.Lane) (he : dataMmaId a b tiles left lane = dataMmaId a b tiles right lane) : left = right := by
  have hleft := data_candidate_mma_at a b tiles left lane hl
  have hright := data_candidate_mma_at a b tiles right lane hr
  rw [he] at hleft
  have hc := (Wgmma.Event.mma.inj (Option.some.inj (hleft.symm.trans hright))).2
  have ho := congrArg Wgmma.Call.ordinal hc
  simpa only [data_call_ordinal] using ho

end
end Ptx.Kernels.HopperDoubleBuffer
