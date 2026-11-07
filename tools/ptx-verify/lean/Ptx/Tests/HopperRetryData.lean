import Ptx.Kernels.HopperDoubleBufferRetryDataReads
import Ptx.Tests.HopperRetryPrefetch

/-! Independent real data with nonzero heterogeneous retries. Positive joint
TMA/control/tensor and explicit RF value witnesses replace the earlier known
bits/realPart mismatch; full memory/coherence admission remains separate. -/
namespace Ptx.HopperRetryDataTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev schedule := HopperRetryPrefetchTests.schedule
abbrev family (a b) := retryDataFamily a b 3 schedule
abbrev candidate (a b) := retryDataCandidate a b 3 schedule
abbrev frame : Location → Symbolic.Byte := fun _ => .bits (byte 17)

theorem actual_query_metadata :
    List.ofFn (fun t : Fin 3 => (retryDataNativeQuery 3 schedule 0 t,retryDataNativeQuery 3 schedule 2 t,
      retryDataCopyQuery 3 schedule t 0,retryDataCopyQuery 3 schedule t 1)) =
      [(10,4,0,2),(19,11,6,8),(25,19,15,17)] := by decide

theorem actual_failed_and_successful_waits (a b) (tile : Fin 3) (lane : Wgmma.Lane) :
    (∀ attempt < schedule lane tile, (retryDataOracle a b 3 schedule lane).base.wait (retryDataQuery 3 schedule lane tile+attempt) = false) ∧
    (retryDataOracle a b 3 schedule lane).base.wait (retryDataWaitQuery 3 schedule lane tile) = true :=
  ⟨fun _ ha => retry_data_failed_wait a b 3 schedule lane tile _ ha,retry_data_successful_wait a b 3 schedule lane tile tile.isLt⟩

theorem positive_joint_components (a b) :
    Unified.TmaComponents code (completeLaunch 3 (dataRepresentedInitial a b 3 frame)) (candidate a b) Tma.localShared (dataMaps 3) (retryHistories (family a b)) ∧
    Unified.ControlAdmitted HopperStage.block (candidate a b) (retryHistories (family a b)) ∧
    ∀ tile < 3, Wgmma.TensorConditions .zero ((family a b).calls tile) (dataSharedTile a b tile) :=
  retry_data_tma_control_tensor_components a b 3 schedule frame (by decide) (by decide)

theorem positive_read_agreement (a b) :
    Unified.ReadAgreement Tma.localShared Access.globalDescriptor (candidate a b) (dataInitialProxyMemory a b 3 frame)
      (Unified.Eligible Tma.localShared Access.globalDescriptor (candidate a b) (retryHistories (family a b)) dataCluster
        (retryDataReadWitness a b 3 schedule)) (retryDataReadWitness a b 3 schedule) :=
  retry_data_read_witness_agreement a b 3 schedule frame (by decide) (by decide)

theorem actual_current_rf (a b) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    retryDataReadWitness a b 3 schedule (retryNativeRead (family a b) tile operand) (retryNativeLocation (family a b) tile operand) =
      some (retryNativeProducer (family a b) tile operand) :=
  retry_data_read_witness_current a b 3 schedule tile tile.isLt (by decide) (by decide) operand

theorem actual_a_producer_value (a b) (tile : Fin 3) (p : Wgmma.ACoord) (part : Fin 2) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) (retryNativeProducer (family a b) tile (.a p part))
      (retryNativeLocation (family a b) tile (.a p part)) = some (.realPart .f16 (a tile p) part.val) := by
  have hp := retry_data_producer_storage a b 3 schedule tile tile.isLt (by decide) (by decide) (.a p part)
  have ha := retry_data_call_agreement a b 3 schedule tile 0 tile.isLt (.a p part)
  have hv := (retry_data_call_values a b 3 schedule tile 0 tile.isLt).1 p part
  change ((family a b).calls tile 0).operandBytes (Wgmma.OperandByte.a p part).index =
    dataSharedTile a b tile (retryNativeLocation (family a b) tile (.a p part)) at ha
  rw [← ha,hv] at hp
  exact hp

theorem actual_b_producer_value (a b) (tile : Fin 3) (p : Wgmma.BCoord) (part : Fin 2) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) (retryNativeProducer (family a b) tile (.b p part))
      (retryNativeLocation (family a b) tile (.b p part)) = some (.realPart .f16 (b tile p) part.val) := by
  have hp := retry_data_producer_storage a b 3 schedule tile tile.isLt (by decide) (by decide) (.b p part)
  have ha := retry_data_call_agreement a b 3 schedule tile 0 tile.isLt (.b p part)
  have hv := (retry_data_call_values a b 3 schedule tile 0 tile.isLt).2 p part
  change ((family a b).calls tile 0).operandBytes (Wgmma.OperandByte.b p part).index =
    dataSharedTile a b tile (retryNativeLocation (family a b) tile (.b p part)) at ha
  rw [← ha,hv] at hp
  exact hp

theorem actual_native_read_values (a b) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    Unified.readByte Tma.localShared Access.globalDescriptor (candidate a b) (retryNativeRead (family a b) tile operand)
      (retryNativeLocation (family a b) tile operand) = some (((family a b).calls tile 0).operandBytes operand.index) ∧
    Unified.sourceValue Tma.localShared Access.globalDescriptor (candidate a b) (dataInitialProxyMemory a b 3 frame)
      (retryNativeRead (family a b) tile operand) (retryNativeLocation (family a b) tile operand)
      (retryDataReadWitness a b 3 schedule (retryNativeRead (family a b) tile operand) (retryNativeLocation (family a b) tile operand)) =
        some (((family a b).calls tile 0).operandBytes operand.index) := by
  have hr := retry_native_read_byte (family a b) (retry_data_source a b 3 schedule (dataRepresentedInitial a b 3 frame) (by decide) (by decide)) tile tile.isLt operand
  exact ⟨hr,retry_data_read_witness_value a b 3 schedule frame (by decide) (by decide) _ _ _ hr⟩

theorem nonzero_three_tile_accumulation (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    (replyCheckpoint 3 lane (retryDataOracle (fun _ _ => 1) (fun _ _ => 2) 3 schedule lane) (schedule lane)).2 slot = 96 := by
  rw [retry_data_final_accumulation]
  norm_num [specification]

theorem bits_payload_rejected (tile : Fin 3) (p : Wgmma.ACoord) (part : Fin 2) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (candidate (fun _ _ => 1) (fun _ _ => 2))
      (retryNativeProducer (family (fun _ _ => 1) (fun _ _ => 2)) tile (.a p part))
      (retryNativeLocation (family (fun _ _ => 1) (fun _ _ => 2)) tile (.a p part)) ≠ some (.bits (byte 0)) := by
  rw [actual_a_producer_value]
  intro he
  cases he

abbrev distinctA : TileA := fun tile _ => tile
abbrev distinctB : TileB := fun _ _ => 1
def staleRf : Unified.ReadsFrom := fun _ _ => some (retryNativeProducer (family distinctA distinctB) 0 (.a ⟨0,0⟩ 0))

theorem stale_reused_tile_read_rejected :
    ¬Unified.ReadAgreement Tma.localShared Access.globalDescriptor (candidate distinctA distinctB) (dataInitialProxyMemory distinctA distinctB 3 frame)
      (Unified.Eligible Tma.localShared Access.globalDescriptor (candidate distinctA distinctB) (retryHistories (family distinctA distinctB)) dataCluster staleRf) staleRf := by
  intro ha
  let operand : Wgmma.OperandByte := .a ⟨0,0⟩ 0
  have hw := retry_data_source distinctA distinctB 3 schedule (dataRepresentedInitial distinctA distinctB 3 frame) (by decide) (by decide)
  have he := retry_native_eligible (family distinctA distinctB) hw (retry_data_complete distinctA distinctB 3 schedule (by decide) (by decide))
    (retry_data_descriptors distinctA distinctB 3 schedule (by decide) (by decide)) (by decide) 2 (by decide) staleRf operand
  have hr := retry_native_read_byte (family distinctA distinctB) hw 2 (by decide) operand
  have hv := ha _ _ _ he hr
  change Unified.writeByte Tma.localShared Access.globalDescriptor (candidate distinctA distinctB)
    (retryNativeProducer (family distinctA distinctB) 0 operand) (retryNativeLocation (family distinctA distinctB) 2 operand) =
      some (((family distinctA distinctB).calls 2 0).operandBytes operand.index) at hv
  rw [← retry_native_location_same_stage (family distinctA distinctB) 0 2 (by decide) operand] at hv
  have hp := actual_a_producer_value distinctA distinctB (0 : Fin 3) ⟨0,0⟩ 0
  norm_num only [distinctA,Fin.val_zero] at hp
  change Unified.writeByte Tma.localShared Access.globalDescriptor (candidate distinctA distinctB)
    (retryNativeProducer (family distinctA distinctB) 0 operand) (retryNativeLocation (family distinctA distinctB) 0 operand) = some (.realPart .f16 0 0) at hp
  rw [hp] at hv
  have hoperand := (retry_data_call_values distinctA distinctB 3 schedule 2 0 (by decide)).1 ⟨0,0⟩ 0
  norm_num only [distinctA,Fin.val_zero] at hoperand
  change ((family distinctA distinctB).calls 2 0).operandBytes operand.index = .realPart .f16 2 0 at hoperand
  rw [hoperand] at hv
  norm_num at hv

theorem copy_roles_cannot_alias :
    retryDataCopyQuery 3 schedule 2 0 ≠ retryDataCopyQuery 3 schedule 0 1 := by decide

end
end Ptx.HopperRetryDataTests
