import Ptx.Kernels.HopperDoubleBufferObservedOutput
import Ptx.Hopper.UnifiedTensorMemory

/-! Repeated native tensor inputs derived through admitted actual RF and TMA
bytes, with arbitrary compatible memory witnesses. Arithmetic admission is
checked separately. This does not reconstruct arbitrary source executions.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_native_producer_storage (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) (operand : Wgmma.OperandByte) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataNativeProducer a b tiles tile operand) (dataNativeLocation a b tiles tile operand) =
      some (dataSharedTile a b tile (dataNativeLocation a b tiles tile operand)) := by
  cases operand with
  | a p byte =>
    rw [data_native_a_location]
    exact Access.tensor_write (descriptor := Access.globalDescriptor) (data_transfer_a_location a b tiles tile ht hb (Wgmma.aOffset (p,byte)))
      (data_transfer_a_byte a b tiles tile ht hb (Wgmma.aOffset (p,byte)))
  | b p byte =>
    rw [data_native_b_location]
    exact Access.tensor_write (descriptor := Access.globalDescriptor) (data_transfer_b_location a b tiles tile ht hb (Wgmma.bOffset (p,byte)))
      (data_transfer_b_byte a b tiles tile ht hb (Wgmma.bOffset (p,byte)))

theorem data_tensor_inputs_from_memory {a b tiles tile initial rf co} (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      initial rf co (dataHistories a b tiles) dataCluster) :
    Wgmma.InputAgreement .zero (dataIterationCall a b tiles tile 0) (dataSharedTile a b tile) :=
  Unified.collective_input_from_sources (dataCollective a b tiles tile ht) hc.toCausalConstraints
    (dataNativeProducer a b tiles tile) (data_native_eligibility_derived a b tiles tile ht hb rf)
    (data_native_rf_forced ht hb hc) (data_native_producer_storage a b tiles tile ht hb)

theorem data_tensor_component_from_memory {a b tiles tile initial rf co} (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      initial rf co (dataHistories a b tiles) dataCluster) :
    Wgmma.TensorConditions .zero (dataIterationCall a b tiles tile) (dataSharedTile a b tile) := by
  have ha : Wgmma.MatrixDescriptor.Packed (dataIterationCall a b tiles tile 0).a := by
    rw [data_call_a]; exact (descriptor_profiles (stage tile)).1
  have hb' : Wgmma.MatrixDescriptor.Packed (dataIterationCall a b tiles tile 0).b := by
    rw [data_call_b]; exact (descriptor_profiles (stage tile)).2
  exact Unified.collective_tensor_from_representative (dataCollective a b tiles tile ht)
    ha hb' (data_tensor_inputs_from_memory ht hb hc) (data_call_storage a b tiles tile 0)
    ⟨a tile,b tile,fun lane => data_call_input_values a b tiles tile lane ht,data_calls_arithmetic a b tiles tile ht⟩

theorem data_tensor_result_from_memory {a b tiles tile initial rf co} (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      initial rf co (dataHistories a b tiles) dataCluster) :
    Wgmma.scatterC (fun p => (dataIterationCall a b tiles tile p.1).output p.2) =
      Wgmma.matrixStep (a tile) (b tile) (result a b tile) := by
  apply Unified.collective_arithmetic_result_from_memory (dataCollective a b tiles tile ht) hc.toCausalConstraints
    (dataNativeProducer a b tiles tile) (data_native_eligibility_derived a b tiles tile ht hb rf)
    (data_native_rf_forced ht hb hc) (data_native_producer_storage a b tiles tile ht hb)
    (data_call_storage a b tiles tile 0)
    ⟨a tile,b tile,fun lane => data_call_input_values a b tiles tile lane ht,data_calls_arithmetic a b tiles tile ht⟩
  intro p
  exact data_call_input a b tiles tile p.1 ht p.2

theorem data_memory_tensor_observer_components (a b tiles frame) (hb : tiles ≤ 2^28) :
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataInitialProxyMemory a b tiles frame) (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles)
      (dataHistories a b tiles) dataCluster ∧
    (∀ tile < tiles, Wgmma.TensorConditions .zero (dataIterationCall a b tiles tile) (dataSharedTile a b tile)) ∧
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataInitialProxyMemory a b tiles frame) (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles)
      (dataHistories a b tiles) dataCluster (dataObservation a b tiles frame) :=
  ⟨data_memory_witness a b tiles frame hb,
    fun _ ht => data_tensor_component_from_memory ht hb (data_memory_witness a b tiles frame hb),data_observer_witness a b tiles frame hb⟩

end
end Ptx.Kernels.HopperDoubleBuffer
