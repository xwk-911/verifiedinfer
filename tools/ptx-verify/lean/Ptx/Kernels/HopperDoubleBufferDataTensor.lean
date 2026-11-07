import Ptx.Kernels.HopperDoubleBufferDataCalls

/-! Tensor component of the actual source call cohort for arbitrary tiles.
The memory below is a logical per-tile shared view. Relating it to TMA writes,
completion/publication and repeated source-matched RF/co remains mandatory.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataSharedTile (a : TileA) (b : TileB) (tile : Nat) (location : Location) : Symbolic.Byte :=
  Wgmma.tileMemory .zero (a tile) (b tile) ⟨location.space,location.address-aBase (stage tile)⟩

theorem data_call_storage (a b tiles tile lane) :
    Wgmma.MatrixStorage .zero (dataIterationCall a b tiles tile lane) (dataSharedTile a b tile) (a tile) (b tile) := by
  constructor
  · intro p byte
    simp only [Wgmma.operandLocation]
    rw [data_call_a,a_operand_address]
    simpa only [dataSharedTile,Wgmma.tileMemory,ite_true,Nat.add_sub_cancel_left] using Wgmma.tile_byte_a (a tile) (b tile) p byte
  · intro p byte
    simp only [Wgmma.operandLocation]
    rw [data_call_b,b_operand_address]
    have hs : bBase (stage tile)+(Wgmma.bOffset (p,byte)).val-aBase (stage tile) = 2048+(Wgmma.bOffset (p,byte)).val := by
      dsimp [aBase,bBase]
      omega
    simpa only [dataSharedTile,Wgmma.tileMemory,ite_true,hs] using Wgmma.tile_byte_b (a tile) (b tile) p byte

theorem data_call_agreement (a b tiles tile lane) (ht : tile < tiles) :
    Wgmma.InputAgreement .zero (dataIterationCall a b tiles tile lane) (dataSharedTile a b tile) := by
  have hs := data_call_storage a b tiles tile lane
  intro operand
  cases operand with
  | a p byte =>
    rw [data_call_operands a b tiles tile lane ht]
    exact (Wgmma.payload_a (a tile) (b tile) p byte).trans (hs.1 p byte).symm
  | b p byte =>
    rw [data_call_operands a b tiles tile lane ht]
    exact (Wgmma.payload_b (a tile) (b tile) p byte).trans (hs.2 p byte).symm

theorem data_tensor_component (a b tiles tile) (ht : tile < tiles) :
    Wgmma.TensorConditions .zero (dataIterationCall a b tiles tile) (dataSharedTile a b tile) := {
  cohort := data_calls_cohort a b tiles tile
  aProfile := by rw [data_call_a]; exact (descriptor_profiles (stage tile)).1
  bProfile := by rw [data_call_b]; exact (descriptor_profiles (stage tile)).2
  agreement := fun lane => data_call_agreement a b tiles tile lane ht
  tensor := ⟨a tile,b tile,fun lane => data_call_input_values a b tiles tile lane ht,data_calls_arithmetic a b tiles tile ht⟩
}

theorem data_tensor_step (a b tiles tile) (ht : tile < tiles) :
    Wgmma.scatterC (fun p => (dataIterationCall a b tiles tile p.1).output p.2) =
      Wgmma.matrixStep (a tile) (b tile) (result a b tile) := by
  apply Wgmma.tensor_correct_accumulator (data_tensor_component a b tiles tile ht) (data_call_storage a b tiles tile 0)
  intro p
  exact data_call_input a b tiles tile p.1 ht p.2

end
end Ptx.Kernels.HopperDoubleBuffer
