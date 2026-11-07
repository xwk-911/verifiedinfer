import Ptx.Kernels.HopperDoubleBufferMemoryInputs
import Ptx.Tests.HopperDoubleBufferData

/-! Repeated actual shared writers, phase order and conditional RF rules.
The full memory/no-mixed-size premises are retained. No memory witness is
assumed to exist by these tests; finite rejection checks use metadata only. -/
namespace Ptx.HopperDoubleBufferMemoryPhaseTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev a := HopperDoubleBufferDataTests.a
abbrev b := HopperDoubleBufferDataTests.b
def shapeAt (tiles : Nat) (lane : Wgmma.Lane) (serial : Nat) : Option Bool :=
  ((dataCompleteCandidate a b tiles).view.eventAt ⟨(ctx tiles lane).id,serial⟩).map memoryShape
def nonbulkAt (tiles : Nat) (lane : Wgmma.Lane) (serial : Nat) : Bool :=
  (Access.copyAt (dataCompleteCandidate a b tiles).view ⟨(ctx tiles lane).id,serial⟩).isSome
def copyDestination (tiles tile : Nat) (isA : Bool) (offset : Nat) : Option Nat :=
  (Tma.writeLocation Tma.localShared (dataCompleteCandidate a b tiles).view
    (if isA then dataCopyAId a b tiles tile else dataCopyBId a b tiles tile) offset).map Location.address
def addressAt (tiles tile : Nat) (operand : Wgmma.OperandByte) : Nat := (dataNativeLocation a b tiles tile operand).address

theorem actual_initial_memory_shape : shapeAt 3 0 0 = some true ∧ shapeAt 3 127 0 = some true := by decide
theorem actual_compute_memory_shape : shapeAt 3 0 13 = some true ∧ shapeAt 3 127 4 = some true := by decide
theorem actual_output_memory_shape : shapeAt 3 0 35 = some true ∧ shapeAt 3 127 23 = some true := by decide
theorem tma_is_not_nonbulk : nonbulkAt 3 0 6 = false ∧ nonbulkAt 3 0 20 = false := by decide
theorem native_is_not_nonbulk : nonbulkAt 3 127 4 = false ∧ nonbulkAt 3 0 13 = false := by decide
theorem a_copy_byte_boundaries : copyDestination 3 2 true 0 = some 16 ∧ copyDestination 3 2 true 2047 = some 2063 ∧ copyDestination 3 2 true 2048 = none := by decide
theorem b_copy_byte_boundaries : copyDestination 3 2 false 0 = some 2064 ∧ copyDestination 3 2 false 255 = some 2319 ∧ copyDestination 3 2 false 256 = none := by decide
theorem opposite_slot_byte_boundaries : copyDestination 3 1 true 0 = some 2320 ∧ copyDestination 3 1 false 255 = some 4623 := by decide
theorem physical_reuse_keeps_address : addressAt 3 0 (.a (0,0) 0) = 16 ∧ addressAt 3 2 (.a (0,0) 0) = 16 := by decide
theorem operands_have_disjoint_regions : addressAt 3 2 (.a (63,15) 1) = 2063 ∧ addressAt 3 2 (.b (0,0) 0) = 2064 := by decide
theorem zero_path_has_no_tensor_copy : copyDestination 0 0 true 0 = none := by decide
theorem ordinary_shared_store_rejected_by_envelope : memoryShape (.ampere (.ordinary (.write ⟨.shared .zero,16⟩ []))) = false := by decide
theorem ordinary_shared_load_rejected_by_envelope : memoryShape (.ampere (.ordinary (.read ⟨.shared .zero,16⟩ []))) = false := by decide

theorem multiple_actual_writers : ∃ left right lv rv, left ≠ right ∧
    Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3) left
      (dataNativeLocation a b 3 2 (.a (0,0) 0)) = some lv ∧
    Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3) right
      (dataNativeLocation a b 3 2 (.a (0,0) 0)) = some rv := by
  refine ⟨dataNativeProducer a b 3 0 (.a (0,0) 0),dataNativeProducer a b 3 2 (.a (0,0) 0),
    (dataIterationCall a b 3 0 0).operandBytes (Wgmma.OperandByte.a (0,0) 0).index,
    (dataIterationCall a b 3 2 0).operandBytes (Wgmma.OperandByte.a (0,0) 0).index,by decide,?_,?_⟩
  · have hw := data_native_producer_write a b 3 0 (by decide) (by decide) (.a (0,0) 0)
    rw [data_native_same_slot_location a b 3 0 2 (by decide) (.a (0,0) 0)] at hw
    exact hw
  · exact data_native_producer_write a b 3 2 (by decide) (by decide) (.a (0,0) 0)

theorem global_unique_writer_assumption_rejected :
    ¬(∀ left right lv rv,
      Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3) left
        (dataNativeLocation a b 3 2 (.a (0,0) 0)) = some lv →
      Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3) right
        (dataNativeLocation a b 3 2 (.a (0,0) 0)) = some rv → left = right) := by
  intro h
  obtain ⟨left,right,lv,rv,hne,hl,hr⟩ := multiple_actual_writers
  exact hne (h left right lv rv hl hr)

theorem initial_only_co_rejected (rf : Unified.ReadsFrom) :
    ¬Unified.Coherent Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3)
      (dataHistories a b 3) dataCluster rf (Unified.InitialCo Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3)) :=
  data_repeated_initial_co_rejected a b 3 0 2 (by decide) (by decide) (by decide) (by decide) rf (.a (0,0) 0)

theorem arbitrary_real_writer_inventory (x : TileA) (y : TileB) (tiles tile : Nat) (hb : tiles ≤ 2^28)
    (operand : Wgmma.OperandByte) (writer : Unified.Node) (value : Symbolic.Byte)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles) writer
      (dataNativeLocation x y tiles tile operand) = some value) :
    ∃ source < tiles, stage source = stage tile ∧ writer = dataNativeProducer x y tiles source operand :=
  data_native_writer_case hb hw

theorem arbitrary_real_untainted (x : TileA) (y : TileB) (tiles tile : Nat) (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (rf : Unified.ReadsFrom) (operand : Wgmma.OperandByte) :
    ¬Unified.Tainted Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles) (dataHistories x y tiles)
      dataCluster rf (dataNativeRead x y tiles tile operand) (dataNativeLocation x y tiles tile operand) :=
  data_native_not_tainted x y tiles tile ht hb rf operand

theorem nonadjacent_write_order (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 5) (dataHistories a b 5) dataCluster
      (dataNativeLocation a b 5 0 operand) (dataNativeProducer a b 5 0 operand) (dataNativeProducer a b 5 4 operand) :=
  data_native_writes_order a b 5 0 4 (by decide) (by decide) (by decide) (by decide) operand

theorem current_rf_conditional {initial rf co}
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 5) initial rf co (dataHistories a b 5) dataCluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 5) (dataHistories a b 5) dataCluster rf)
    (operand : Wgmma.OperandByte) :
    rf (dataNativeRead a b 5 4 operand) (dataNativeLocation a b 5 4 operand) = some (dataNativeProducer a b 5 4 operand) :=
  data_native_reads_from_current (a := a) (b := b) (tiles := 5) (tile := 4) (by decide) (by decide) hc hm operand

theorem stale_rf_after_wrap_rejected {initial rf co}
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 5) initial rf co (dataHistories a b 5) dataCluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 5) (dataHistories a b 5) dataCluster rf)
    (operand : Wgmma.OperandByte) :
    rf (dataNativeRead a b 5 4 operand) (dataNativeLocation a b 5 4 operand) ≠ some (dataNativeProducer a b 5 0 operand) :=
  data_native_stale_source_rejected (a := a) (b := b) (tiles := 5) (tile := 4) (old := 0)
    (by decide) (by decide) (by decide) (by decide) hc hm operand

theorem future_rf_rejected {initial rf co}
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3) initial rf co (dataHistories a b 3) dataCluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3) (dataHistories a b 3) dataCluster rf)
    (operand : Wgmma.OperandByte) :
    rf (dataNativeRead a b 3 0 operand) (dataNativeLocation a b 3 0 operand) ≠ some (dataNativeProducer a b 3 2 operand) :=
  data_native_future_source_rejected (a := a) (b := b) (tiles := 3) (tile := 0) (next := 2)
    (by decide) (by decide) (by decide) (by decide) hc hm operand

end
end Ptx.HopperDoubleBufferMemoryPhaseTests
