import Ptx.Kernels.HopperDoubleBufferRetryDataOracle

/-! Actual source tensor calls for independently supplied real matrices and
arbitrary finite retries. Inputs, operands and outputs follow the constructed
oracle and source checkpoints; memory/RF admission remains separate. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_data_call_output (a b tiles schedules tile lane) (ht : tile < tiles) (slot : Wgmma.Slot) :
    ((retryDataFamily a b tiles schedules).calls tile lane).output slot = result a b (tile+1) (Wgmma.cCoord (lane,slot)) := by
  change (retryDataOracle a b tiles schedules lane).matrix
    (preparedState (replyTileCheckpoint tiles lane (retryDataOracle a b tiles schedules lane) (schedules lane) tile).1
      tile tiles (schedules lane tile) (HopperStage.leader lane)).base.scalar.core.queries slot = _
  rw [retry_reply_prepared_query]
  exact retry_data_native_matrix a b tiles schedules lane tile ht slot

theorem retry_data_call_operands (a b tiles schedules tile lane) (ht : tile < tiles) (offset : Nat) :
    ((retryDataFamily a b tiles schedules).calls tile lane).operandBytes offset = Wgmma.payload (a tile) (b tile) offset := by
  change (retryDataOracle a b tiles schedules lane).operands
    (preparedState (replyTileCheckpoint tiles lane (retryDataOracle a b tiles schedules lane) (schedules lane) tile).1
      tile tiles (schedules lane tile) (HopperStage.leader lane)).base.scalar.core.queries offset = _
  rw [retry_reply_prepared_query]
  exact retry_data_native_operands a b tiles schedules lane tile ht offset

theorem retry_data_checkpoint_values (a b tiles schedules tile lane) (ht : tile ≤ tiles) (slot : Wgmma.Slot) :
    (replyTileCheckpoint tiles lane (retryDataOracle a b tiles schedules lane) (schedules lane) tile).2 slot =
      result a b tile (Wgmma.cCoord (lane,slot)) := by
  cases tile with
  | zero => rfl
  | succ tile =>
    rw [← reply_call_output_checkpoint]
    exact retry_data_call_output a b tiles schedules tile lane (by omega) slot

theorem retry_data_call_input (a b tiles schedules tile lane) (ht : tile < tiles) (slot : Wgmma.Slot) :
    ((retryDataFamily a b tiles schedules).calls tile lane).input slot = result a b tile (Wgmma.cCoord (lane,slot)) :=
  retry_data_checkpoint_values a b tiles schedules tile lane (by omega) slot

theorem retry_data_call_values (a b tiles schedules tile lane) (ht : tile < tiles) :
    Wgmma.InputValues ((retryDataFamily a b tiles schedules).calls tile lane) (a tile) (b tile) := by
  constructor
  · intro p part
    rw [retry_data_call_operands a b tiles schedules tile lane ht]
    exact Wgmma.payload_a _ _ _ _
  · intro p part
    rw [retry_data_call_operands a b tiles schedules tile lane ht]
    exact Wgmma.payload_b _ _ _ _

theorem retry_data_calls_arithmetic (a b tiles schedules tile) (ht : tile < tiles) :
    Wgmma.Arithmetic (a tile) (b tile)
      (fun p => ((retryDataFamily a b tiles schedules).calls tile p.1).input p.2)
      (fun p => ((retryDataFamily a b tiles schedules).calls tile p.1).output p.2) := by
  have hin : (fun p => ((retryDataFamily a b tiles schedules).calls tile p.1).input p.2) = Wgmma.gatherC (result a b tile) := by
    funext p
    exact retry_data_call_input a b tiles schedules tile p.1 ht p.2
  intro p
  change ((retryDataFamily a b tiles schedules).calls tile p.1).output p.2 =
    Wgmma.results (a tile) (b tile) (fun p => ((retryDataFamily a b tiles schedules).calls tile p.1).input p.2) p
  rw [hin,retry_data_call_output a b tiles schedules tile p.1 ht p.2]
  exact (tile_reply_value a b tile p).symm

theorem retry_data_call_agreement (a b tiles schedules tile lane) (ht : tile < tiles) :
    Wgmma.InputAgreement .zero ((retryDataFamily a b tiles schedules).calls tile lane) (dataSharedTile a b tile) := by
  have hv := retry_data_call_values a b tiles schedules tile lane ht
  have hs := retry_call_storage (retryDataFamily a b tiles schedules) a b tile
  have hl : Wgmma.MatrixStorage .zero ((retryDataFamily a b tiles schedules).calls tile lane) (dataSharedTile a b tile) (a tile) (b tile) := by
    change Wgmma.MatrixStorage .zero (replyCall tiles 0 (retryDataOracle a b tiles schedules 0) (schedules 0) tile) _ _ _ at hs
    change Wgmma.MatrixStorage .zero (replyCall tiles lane (retryDataOracle a b tiles schedules lane) (schedules lane) tile) _ _ _
    simpa only [Wgmma.MatrixStorage,Wgmma.operandLocation,reply_call_a,reply_call_b] using hs
  intro operand
  cases operand with
  | a p part => exact (hv.1 p part).trans (hl.1 p part).symm
  | b p part => exact (hv.2 p part).trans (hl.2 p part).symm

theorem retry_data_tensor_component (a b tiles schedules tile) (ht : tile < tiles) :
    Wgmma.TensorConditions .zero ((retryDataFamily a b tiles schedules).calls tile) (dataSharedTile a b tile) := {
  cohort := reply_calls_cohort tiles tile (retryDataOracle a b tiles schedules) schedules
  aProfile := by rw [show ((retryDataFamily a b tiles schedules).calls tile 0).a = aDescriptor (stage tile) from reply_call_a _ _ _ _ _]; exact (descriptor_profiles _).1
  bProfile := by rw [show ((retryDataFamily a b tiles schedules).calls tile 0).b = bDescriptor (stage tile) from reply_call_b _ _ _ _ _]; exact (descriptor_profiles _).2
  agreement := fun lane => retry_data_call_agreement a b tiles schedules tile lane ht
  tensor := ⟨a tile,b tile,fun lane => retry_data_call_values a b tiles schedules tile lane ht,retry_data_calls_arithmetic a b tiles schedules tile ht⟩
}

theorem retry_data_final_accumulation (a b tiles schedules lane slot) :
    (replyCheckpoint tiles lane (retryDataOracle a b tiles schedules lane) (schedules lane)).2 slot =
      specification a b tiles (Wgmma.cCoord (lane,slot)) := by
  apply reply_final_accumulation tiles (retryDataOracle a b tiles schedules) schedules a b
  exact fun tile ht => retry_data_calls_arithmetic a b tiles schedules tile ht

end
end Ptx.Kernels.HopperDoubleBuffer
