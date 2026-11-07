import Ptx.Kernels.HopperDoubleBufferRetryNativeReuse
import Ptx.Tests.HopperRetryAdmission

/-! Actual native publication/completion/reuse on the descriptor-admitted
three-tile heterogeneous nonzero-retry source. These are model byte edges,
not causal RF/co, native-control, tensor or fully admitted launch tests. -/
namespace Ptx.HopperRetryNativeTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev candidate := HopperRetryAdmissionTests.candidate
abbrev family := HopperRetryAdmissionTests.family
abbrev source := HopperRetryAdmissionTests.source_well_formed
abbrev descriptors := HopperRetryAdmissionTests.actual_descriptor_admission

theorem all_operand_publications (value : ℝ) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    Unified.NativePublished Tma.localShared (candidate value) (retryHistories (family value)) dataCluster
      (retryNativeLocation (family value) tile operand) (retryNativeProducer (family value) tile operand) (retryNativeRead (family value) tile operand) :=
  retry_native_publication (family value) (by decide) (source value (fun _ => .bits (byte 0))) (descriptors value) tile tile.isLt operand

theorem all_operand_byte_order (value : ℝ) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate value) (retryHistories (family value)) dataCluster
      (retryNativeLocation (family value) tile operand) (retryNativeProducer (family value) tile operand) (retryNativeRead (family value) tile operand) :=
  retry_native_byte_order (family value) (by decide) (source value (fun _ => .bits (byte 0))) (descriptors value) tile tile.isLt operand

theorem all_operand_writers_present (value : ℝ) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    ∃ actual, Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value) (retryNativeProducer (family value) tile operand)
      (retryNativeLocation (family value) tile operand) = some actual :=
  retry_native_producer_present (family value) (by decide) (source value (fun _ => .bits (byte 0))) (descriptors value) tile tile.isLt operand

theorem all_native_completions (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) :
    Unified.WgmmaCompletedAt (candidate value) ((family value).mmaId tile 0) ((family value).nativeWaitId tile lane) :=
  retry_native_completed (family value) (source value (fun _ => .bits (byte 0))) (by decide) tile tile.isLt lane

theorem all_native_completion_edges (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate value) (retryHistories (family value)) dataCluster
      (retryNativeLocation (family value) tile operand) (retryNativeRead (family value) tile operand)
      (.base (.tma (.source ((family value).nativeWaitId tile lane)))) :=
  retry_native_completed_order (family value) (source value (fun _ => .bits (byte 0))) (by decide) tile tile.isLt lane operand

theorem producer_native_wait_indices (value : ℝ) :
    ((family value).nativeWaitId 0 0).serial = 16 ∧ ((family value).nativeWaitId 1 0).serial = 28 ∧
      ((family value).nativeWaitId 2 0).serial = 38 := ⟨rfl,rfl,rfl⟩

theorem consumer_native_wait_indices (value : ℝ) :
    ((family value).nativeWaitId 0 2).serial = 9 ∧ ((family value).nativeWaitId 1 2).serial = 20 ∧
      ((family value).nativeWaitId 2 2).serial = 32 := ⟨rfl,rfl,rfl⟩

theorem reuse_wait_precedes_both_issues (value : ℝ) :
    Access.GenericAfter (candidate value).view ((family value).nativeWaitId 0 0) ((family value).copyAId 2).issue ∧
      Access.GenericAfter (candidate value).view ((family value).nativeWaitId 0 0) ((family value).copyBId 2).issue :=
  ⟨retry_native_wait_before_copy_a (family value) (source value (fun _ => .bits (byte 0))) (by decide) 0 2 (by decide) (by decide),
    retry_native_wait_before_copy_b (family value) (source value (fun _ => .bits (byte 0))) (by decide) 0 2 (by decide) (by decide)⟩

theorem all_reused_bytes_protected (value : ℝ) (operand : Wgmma.OperandByte) :
    Unified.NativeReuse Tma.localShared (candidate value) (retryNativeLocation (family value) 0 operand)
      (retryNativeRead (family value) 0 operand) (retryNativeProducer (family value) 2 operand) :=
  retry_native_reuse (family value) (source value (fun _ => .bits (byte 0))) (descriptors value) (by decide)
    0 2 (by decide) (by decide) (by decide) operand

theorem all_reuse_byte_order (value : ℝ) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate value) (retryHistories (family value)) dataCluster
      (retryNativeLocation (family value) 0 operand) (retryNativeRead (family value) 0 operand) (retryNativeProducer (family value) 2 operand) :=
  retry_native_reuse_byte_order (family value) (source value (fun _ => .bits (byte 0))) (descriptors value) (by decide)
    0 2 (by decide) (by decide) (by decide) operand

theorem same_reused_location_different_copy (value : ℝ) (operand : Wgmma.OperandByte) :
    retryNativeLocation (family value) 0 operand = retryNativeLocation (family value) 2 operand ∧
      (family value).copyAId 0 ≠ (family value).copyAId 2 := by
  refine ⟨retry_native_location_same_stage (family value) 0 2 (by decide) operand,?_⟩
  intro he
  have hn := family_copy_a_tile_injective (family value) he
  omega

theorem alternating_arena_has_different_location (value : ℝ) (operand : Wgmma.OperandByte) :
    retryNativeLocation (family value) 0 operand ≠ retryNativeLocation (family value) 1 operand := by
  intro he
  have hh := congrArg Location.address he
  cases operand with
  | a p part =>
    simp only [retryNativeLocation,ReplySourceFamily.calls,reply_operand_a_location] at hh
    change 16+(Wgmma.aOffset (p,part)).val = 2320+(Wgmma.aOffset (p,part)).val at hh
    omega
  | b p part =>
    simp only [retryNativeLocation,ReplySourceFamily.calls,reply_operand_b_location] at hh
    change 2064+(Wgmma.bOffset (p,part)).val = 4368+(Wgmma.bOffset (p,part)).val at hh
    omega

theorem mbarrier_cannot_replace_native_wait (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) (issue : Ptx.Event.EventId) :
    ¬Unified.WgmmaCompletedAt (candidate value) issue ((family value).waitId tile lane) :=
  retry_mbarrier_is_not_native_completion (family value) (source value (fun _ => .bits (byte 0))) tile tile.isLt lane issue

theorem out_of_bounds_a_publication_rejected (value : ℝ) (tile : Fin 3) (issue : Ptx.Event.EventId)
    (operand : Wgmma.OperandByte) (loc : Location) :
    ¬Unified.TmaReady Tma.localShared (candidate value) (retryHistories (family value)) dataCluster
      ((family value).copyAId tile) 2048 issue operand loc := by
  intro hr
  obtain ⟨op,hcopy,ho⟩ := Unified.tma_ready_has_actual_writer hr
  rw [family_copy_a_at (family value) (source value (fun _ => .bits (byte 0))) tile tile.isLt] at hcopy
  have hop := Option.some.inj hcopy
  have hbytes : op.descriptor.bytes = 2048 := by
    rw [← hop,family_copy_a_descriptor (family value) (source value (fun _ => .bits (byte 0))) (descriptors value) tile tile.isLt]
    rfl
  rw [hbytes] at ho
  omega

end
end Ptx.HopperRetryNativeTests
