import Ptx.Kernels.HopperDoubleBufferRetryArithmetic
import Ptx.Tests.HopperRetryAdmission

/-! Checked arithmetic components and source accumulation, including nonzero
arbitrary-real inputs and heterogeneous retries. The existing retry fixture
remains memory-negative (bits payload versus realPart operands); its positive
tensor checks below do not claim full memory/control/execution admission. -/
namespace Ptx.HopperRetryArithmeticTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev family := HopperRetryAdmissionTests.family

theorem arbitrary_real_source_accumulation (a : TileA) (b : TileB) (tiles : Nat)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    (replyCheckpoint tiles lane (dataOracle a b tiles lane) zeroRetries).2 slot =
      specification a b tiles (Wgmma.cCoord (lane,slot)) := by
  apply reply_final_accumulation tiles (dataOracle a b tiles) (fun _ => zeroRetries) a b
  intro tile ht
  exact data_calls_arithmetic a b tiles tile ht

theorem nonzero_three_tile_accumulation (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    (replyCheckpoint 3 lane (dataOracle (fun _ _ => 1) (fun _ _ => 2) 3 lane) zeroRetries).2 slot = 96 := by
  rw [arbitrary_real_source_accumulation]
  norm_num [specification]

theorem zero_matrix_checkpoint (tile : Nat) (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    (replyTileCheckpoint 3 lane ((family 0).replies lane) ((family 0).schedules lane) tile).2 slot = 0 := by
  cases tile <;> rfl

theorem actual_zero_operand_values (value : ℝ) (tile : Nat) (lane : Wgmma.Lane) :
    Wgmma.InputValues ((family value).calls tile lane) (fun _ => 0) (fun _ => 0) := by
  constructor
  · exact Wgmma.payload_a (fun _ => 0) (fun _ => 0)
  · exact Wgmma.payload_b (fun _ => 0) (fun _ => 0)

theorem heterogeneous_retry_tensor_component (tile : Fin 3) :
    Wgmma.TensorConditions .zero ((family 0).calls tile) (dataSharedTile (fun _ _ => 0) (fun _ _ => 0) tile) := by
  apply Unified.collective_tensor_from_representative
    (familyCollective (family 0) (HopperRetryAdmissionTests.source_well_formed 0 (fun _ => .bits (byte 0))) tile (by omega))
    (a := fun _ => 0) (b := fun _ => 0)
  · change Wgmma.MatrixDescriptor.Packed ((family 0).calls tile 0).a
    rw [show ((family 0).calls tile 0).a = aDescriptor (stage tile) from reply_call_a _ _ _ _ _]
    exact (descriptor_profiles _).1
  · change Wgmma.MatrixDescriptor.Packed ((family 0).calls tile 0).b
    rw [show ((family 0).calls tile 0).b = bDescriptor (stage tile) from reply_call_b _ _ _ _ _]
    exact (descriptor_profiles _).2
  · have hv := actual_zero_operand_values 0 tile 0
    have hs := retry_call_storage (family 0) (fun _ _ => 0) (fun _ _ => 0) tile
    intro operand
    cases operand with
    | a p part => exact (hv.1 p part).trans (hs.1 p part).symm
    | b p part => exact (hv.2 p part).trans (hs.2 p part).symm
  · exact retry_call_storage (family 0) (fun _ _ => 0) (fun _ _ => 0) tile
  · refine ⟨fun _ => 0,fun _ => 0,actual_zero_operand_values 0 tile,?_⟩
    change Wgmma.Arithmetic (fun _ => 0) (fun _ => 0)
      (fun p => ((family 0).calls tile p.1).input p.2) (fun p => ((family 0).calls tile p.1).output p.2)
    have hin : (fun p => ((family 0).calls tile p.1).input p.2) = Wgmma.gatherC (fun _ => 0) := by
      funext p
      exact zero_matrix_checkpoint tile p.1 p.2
    intro p
    rw [hin]
    change 0 = Wgmma.results (fun _ => 0) (fun _ => 0) (Wgmma.gatherC (fun _ => 0)) p
    simp [Wgmma.results,Wgmma.gatherC,Wgmma.matrixStep]

theorem heterogeneous_retry_accumulation (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    (replyCheckpoint 3 lane ((family 0).replies lane) ((family 0).schedules lane)).2 slot =
      specification (fun _ _ => 0) (fun _ _ => 0) 3 (Wgmma.cCoord (lane,slot)) := by
  apply reply_final_accumulation 3 (family 0).replies (family 0).schedules (fun _ _ => 0) (fun _ _ => 0)
  intro tile ht
  obtain ⟨a,b,hv,ha⟩ := (heterogeneous_retry_tensor_component ⟨tile,ht⟩).tensor
  obtain ⟨rfl,rfl⟩ := Wgmma.input_values_unique (hv 0) (actual_zero_operand_values 0 tile 0)
  exact ha

theorem fabricated_first_matrix_rejected (memory : Location → Symbolic.Byte) :
    ¬Wgmma.TensorConditions .zero ((family 1).calls 0) memory := by
  intro tensor
  obtain ⟨a,b,hv,ha⟩ := tensor.tensor
  obtain ⟨rfl,rfl⟩ := Wgmma.input_values_unique (hv 0) (actual_zero_operand_values 1 0 0)
  have hin : (fun p => ((family 1).calls 0 p.1).input p.2) = Wgmma.gatherC (fun _ => 0) := rfl
  have hh := ha (0,0)
  rw [hin] at hh
  change (1 : ℝ) = Wgmma.results (fun _ => 0) (fun _ => 0) (Wgmma.gatherC (fun _ => 0)) (0,0) at hh
  norm_num [Wgmma.results,Wgmma.gatherC,Wgmma.matrixStep] at hh

end
end Ptx.HopperRetryArithmeticTests
