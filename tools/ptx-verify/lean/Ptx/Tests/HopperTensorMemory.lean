import Ptx.Kernels.HopperDoubleBufferTensorMemory
import Ptx.Kernels.HopperStageTensorMemory
import Ptx.Tests.HopperDoubleBufferData

/-! The memory/tensor bridge is checked on both actual sources. Negative
proofs distinguish stale/future tiles sharing a physical slot and wrong B
inputs; they do not decide equality of real-valued states or byte payloads.
-/
namespace Ptx.HopperTensorMemoryTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev a := HopperDoubleBufferDataTests.a
abbrev b := HopperDoubleBufferDataTests.b

theorem reused_a_input_from_memory {initial rf co}
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3)
      initial rf co (dataHistories a b 3) dataCluster) :
    (dataIterationCall a b 3 2 0).operandBytes (Wgmma.OperandByte.a (0,0) 0).index = .realPart .f16 3 0 := by
  have hi := data_tensor_inputs_from_memory (tile := 2) (by decide) (by decide) hc
  have hv := Wgmma.input_values_of_memory hi (data_call_storage a b 3 2 0)
  have hx : a 2 (0,0) = 3 := by norm_num [a,HopperDoubleBufferDataTests.a,HopperDoubleBufferTests.nonuniformA]
  simpa only [hx,Fin.val_zero] using hv.1 (0,0) 0

theorem stale_a_tile_rejected {initial rf co}
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3)
      initial rf co (dataHistories a b 3) dataCluster) :
    ¬Wgmma.InputValues (dataIterationCall a b 3 2 0) (a 0) (b 0) := by
  intro hbad
  have hi := data_tensor_inputs_from_memory (tile := 2) (by decide) (by decide) hc
  have hv := Wgmma.input_values_of_memory hi (data_call_storage a b 3 2 0)
  have he := congrFun (Wgmma.input_values_unique hbad hv).1 (0,0)
  norm_num [a,HopperDoubleBufferDataTests.a,HopperDoubleBufferTests.nonuniformA] at he

theorem future_a_tile_rejected {initial rf co}
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3)
      initial rf co (dataHistories a b 3) dataCluster) :
    ¬Wgmma.InputValues (dataIterationCall a b 3 0 0) (a 2) (b 2) := by
  intro hbad
  have hi := data_tensor_inputs_from_memory (tile := 0) (by decide) (by decide) hc
  have hv := Wgmma.input_values_of_memory hi (data_call_storage a b 3 0 0)
  have he := congrFun (Wgmma.input_values_unique hbad hv).1 (0,0)
  norm_num [a,HopperDoubleBufferDataTests.a,HopperDoubleBufferTests.nonuniformA] at he

theorem wrong_b_tile_rejected {initial rf co}
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3)
      initial rf co (dataHistories a b 3) dataCluster) :
    ¬Wgmma.InputValues (dataIterationCall a b 3 2 0) (a 2) (b 0) := by
  intro hbad
  have hi := data_tensor_inputs_from_memory (tile := 2) (by decide) (by decide) hc
  have hv := Wgmma.input_values_of_memory hi (data_call_storage a b 3 2 0)
  have he := congrFun (Wgmma.input_values_unique hbad hv).2 (0,0)
  norm_num [b,HopperDoubleBufferDataTests.b,HopperDoubleBufferTests.nonuniformB] at he

theorem accumulated_point_from_memory {initial rf co}
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3)
      initial rf co (dataHistories a b 3) dataCluster) :
    Wgmma.scatterC (fun p => (dataIterationCall a b 3 2 p.1).output p.2) (0,0) = 20 := by
  have he := congrFun (data_tensor_result_from_memory (tile := 2) (by decide) (by decide) hc) (0,0)
  change _ = result a b 3 (0,0) at he
  exact he.trans HopperDoubleBufferTests.nonuniform_first_three_tiles

theorem incorrect_accumulated_point_rejected {initial rf co}
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3)
      initial rf co (dataHistories a b 3) dataCluster) :
    Wgmma.scatterC (fun p => (dataIterationCall a b 3 2 p.1).output p.2) (0,0) ≠ 21 := by
  rw [accumulated_point_from_memory hc]
  norm_num

theorem one_stage_same_bridge (x : Wgmma.ACoord → ℝ) (y : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) :
    Wgmma.TensorConditions .zero (HopperStage.calls x y) (HopperStage.transferView x y) :=
  HopperStage.stage_tensor_from_memory (HopperStage.stage_causal_witness x y frame)

theorem repeated_compatible_components (x : TileA) (y : TileB) (tiles : Nat) (hb : tiles ≤ 2^28) (frame : Location → Symbolic.Byte) :
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles)
      (dataInitialProxyMemory x y tiles frame) (dataReadWitness x y tiles) (dataCoherenceWitness x y tiles)
      (dataHistories x y tiles) dataCluster ∧
    (∀ tile < tiles, Wgmma.TensorConditions .zero (dataIterationCall x y tiles tile) (dataSharedTile x y tile)) ∧
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles)
      (dataInitialProxyMemory x y tiles frame) (dataReadWitness x y tiles) (dataCoherenceWitness x y tiles)
      (dataHistories x y tiles) dataCluster (dataObservation x y tiles frame) := data_memory_tensor_observer_components x y tiles frame hb

theorem zero_round_tensor_family_empty (frame : Location → Symbolic.Byte) :
    ∀ tile < 0, Wgmma.TensorConditions .zero (dataIterationCall a b 0 tile) (dataSharedTile a b tile) :=
  (data_memory_tensor_observer_components a b 0 frame (by decide)).2.1

end
end Ptx.HopperTensorMemoryTests
