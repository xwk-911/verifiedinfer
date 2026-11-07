import Ptx.Kernels.HopperDoubleBufferRetryTensorInputs
import Ptx.Tests.HopperRetryNative

/-! Actual writer classification/eligibility and concrete bad-memory/RF/co
rejections on the three-tile heterogeneous-retry source. The existing fixture
has bits payloads but realPart operands: its memory conditions are rejected,
not used as a purported positive fully admitted memory/execution witness. -/
namespace Ptx.HopperRetryMemoryTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev candidate := HopperRetryAdmissionTests.candidate
abbrev family := HopperRetryAdmissionTests.family
abbrev source := HopperRetryAdmissionTests.source_well_formed
abbrev complete := HopperRetryAdmissionTests.source_complete
abbrev descriptors := HopperRetryAdmissionTests.actual_descriptor_admission

theorem all_actual_writers_classified (value : ℝ) (tile : Fin 3) (operand : Wgmma.OperandByte) (writer : Unified.Node) (actual : Symbolic.Byte)
    (he : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value) writer (retryNativeLocation (family value) tile operand) = some actual) :
    ∃ written < 3, stage written = stage tile ∧ writer = retryNativeProducer (family value) written operand :=
  retry_native_writer_case (family value) (by decide) (source value (fun _ => .bits (byte 0))) (complete value) (descriptors value) (by decide) he

theorem all_actual_writers_ordered (value : ℝ) (tile : Fin 3) (operand : Wgmma.OperandByte) (writer : Unified.Node) (actual : Symbolic.Byte)
    (he : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value) writer (retryNativeLocation (family value) tile operand) = some actual) :
    writer = retryNativeProducer (family value) tile operand ∨
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate value) (retryHistories (family value)) dataCluster
      (retryNativeLocation (family value) tile operand) writer (retryNativeProducer (family value) tile operand) ∨
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate value) (retryHistories (family value)) dataCluster
      (retryNativeLocation (family value) tile operand) (retryNativeRead (family value) tile operand) writer :=
  retry_native_writer_phase (family value) (source value (fun _ => .bits (byte 0))) (complete value) (descriptors value) (by decide) tile.isLt he

theorem all_native_reads_eligible (value : ℝ) (rf : Unified.ReadsFrom) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    Unified.Eligible Tma.localShared Access.globalDescriptor (candidate value) (retryHistories (family value)) dataCluster rf
      (retryNativeRead (family value) tile operand) (retryNativeLocation (family value) tile operand) :=
  retry_native_eligible (family value) (source value (fun _ => .bits (byte 0))) (complete value) (descriptors value) (by decide) tile tile.isLt rf operand

theorem uninitialized_rf_rejected (value : ℝ) (initial : Unified.ProxyMemory) (co : Location → Option Unified.Node → Option Unified.Node → Prop) :
    ¬Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value) initial (fun _ _ => none) co
      (retryHistories (family value)) dataCluster := by
  intro hm
  have hs := retry_native_reads_from_current (family value) (source value (fun _ => .bits (byte 0))) (complete value) (descriptors value)
    (by decide) hm 0 (by decide) (.a (0,0) 0)
  cases hs

theorem stale_rf_rejected (value : ℝ) (initial : Unified.ProxyMemory) (co : Location → Option Unified.Node → Option Unified.Node → Prop)
    (operand : Wgmma.OperandByte) :
    ¬Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value) initial
      (fun _ _ => some (retryNativeProducer (family value) 0 operand)) co (retryHistories (family value)) dataCluster := by
  intro hm
  exact retry_native_stale_source_rejected (family value) (source value (fun _ => .bits (byte 0))) (complete value) (descriptors value)
    (by decide) hm 2 0 (by decide) (by decide) (by decide) operand rfl

theorem future_rf_rejected (value : ℝ) (initial : Unified.ProxyMemory) (co : Location → Option Unified.Node → Option Unified.Node → Prop)
    (operand : Wgmma.OperandByte) :
    ¬Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value) initial
      (fun _ _ => some (retryNativeProducer (family value) 2 operand)) co (retryHistories (family value)) dataCluster := by
  intro hm
  exact retry_native_future_source_rejected (family value) (source value (fun _ => .bits (byte 0))) (complete value) (descriptors value)
    (by decide) hm 0 2 (by decide) (by decide) (by decide) operand rfl

theorem initialization_only_co_rejected (value : ℝ) (rf : Unified.ReadsFrom) (operand : Wgmma.OperandByte) :
    ¬Unified.Coherent Tma.localShared Access.globalDescriptor (candidate value) (retryHistories (family value)) dataCluster rf
      (Unified.InitialCo Tma.localShared Access.globalDescriptor (candidate value)) :=
  retry_repeated_initial_co_rejected (family value) (source value (fun _ => .bits (byte 0))) (descriptors value) (by decide)
    0 2 (by decide) (by decide) (by decide) rf operand

theorem actual_payload_is_bits (value : ℝ) :
    Tma.transferByte (candidate value).view ((family value).copyAId 0) (Wgmma.aOffset (((0,0) : Wgmma.ACoord),(0 : Fin 2))).val =
      some (.bits (byte 0)) := by
  rw [Tma.transferByte,family_copy_a_at (family value) (source value (fun _ => .bits (byte 0))) 0 (by decide)]
  rfl

theorem fabricated_operand_agreement_rejected (value : ℝ) (initial : Unified.ProxyMemory) (rf : Unified.ReadsFrom)
    (co : Location → Option Unified.Node → Option Unified.Node → Prop) :
    ¬Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate value) initial rf co (retryHistories (family value)) dataCluster := by
  intro hm
  have hw := Access.tensor_write (descriptor := Access.globalDescriptor)
    (retry_operand_a_transfer (family value) (source value (fun _ => .bits (byte 0))) (descriptors value) 0 (by decide) 0 (0,0) 0)
    (actual_payload_is_bits value)
  have hv := retry_native_current_write_value (family value) (source value (fun _ => .bits (byte 0))) (complete value) (descriptors value)
    (by decide) hm 0 (by decide) (.a (0,0) 0)
  have he := Option.some.inj (hw.symm.trans hv)
  change Symbolic.Byte.bits (byte 0) = Symbolic.Byte.realPart .f16 0 0 at he
  cases he

end
end Ptx.HopperRetryMemoryTests
