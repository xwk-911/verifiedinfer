import Ptx.Kernels.HopperDoubleBufferRetryNativeLocations
import Ptx.Hopper.UnifiedNativeWriter

/-! Actual per-byte TMA publication to the source-indexed native collective
for arbitrary finite retries and repeated tiles. Completion observations are
derived from admitted histories. RF/reuse/control/tensor/observer closure is
not a premise silently replaced by this byte-order component. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_a_native_ready {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (hp : tile < tiles) (p : Wgmma.ACoord) (part : Fin 2) :
    Unified.TmaReady Tma.localShared candidate (retryHistories family) dataCluster (family.copyAId tile) (Wgmma.aOffset (p,part)).val
      (family.mmaId tile 0) (.a p part) (Wgmma.operandLocation .zero (family.calls tile 0) (.a p part)) :=
  family_tma_ready_from_observation family hw tile hp (retry_operand_a_transfer family hw hd tile hp 0 p part) rfl
    (retry_a_completion_observed family ht hw hd tile hp)

theorem retry_b_native_ready {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (hp : tile < tiles) (p : Wgmma.BCoord) (part : Fin 2) :
    Unified.TmaReady Tma.localShared candidate (retryHistories family) dataCluster (family.copyBId tile) (Wgmma.bOffset (p,part)).val
      (family.mmaId tile 0) (.b p part) (Wgmma.operandLocation .zero (family.calls tile 0) (.b p part)) :=
  family_tma_ready_from_observation family hw tile hp (retry_operand_b_transfer family hw hd tile hp 0 p part) rfl
    (retry_b_completion_observed family ht hw hd tile hp)

def retryNativeRead {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (operand : Wgmma.OperandByte) : Unified.Node :=
  .wgmmaRead (family.mmaId tile 0) operand
def retryNativeProducer {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) : Wgmma.OperandByte → Unified.Node
  | .a p part => .base (.tma (.write (family.copyAId tile) (Wgmma.aOffset (p,part)).val))
  | .b p part => .base (.tma (.write (family.copyBId tile) (Wgmma.bOffset (p,part)).val))
def retryNativeLocation {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (operand : Wgmma.OperandByte) : Location :=
  Wgmma.operandLocation .zero (family.calls tile 0) operand

theorem retry_native_publication {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (hp : tile < tiles) (operand : Wgmma.OperandByte) :
    Unified.NativePublished Tma.localShared candidate (retryHistories family) dataCluster
      (retryNativeLocation family tile operand) (retryNativeProducer family tile operand) (retryNativeRead family tile operand) := by
  cases operand with
  | a p part => exact retry_a_native_ready family ht hw hd tile hp p part
  | b p part => exact retry_b_native_ready family ht hw hd tile hp p part

theorem retry_native_byte_order {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (hp : tile < tiles) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate (retryHistories family) dataCluster
      (retryNativeLocation family tile operand) (retryNativeProducer family tile operand) (retryNativeRead family tile operand) :=
  Unified.native_published_byte_order (retry_native_publication family ht hw hd tile hp operand)

theorem retry_native_producer_present {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (hp : tile < tiles) (operand : Wgmma.OperandByte) :
    ∃ value, Unified.writeByte Tma.localShared Access.globalDescriptor candidate (retryNativeProducer family tile operand)
      (retryNativeLocation family tile operand) = some value := by
  cases operand with
  | a p part => exact Unified.tma_ready_writer_byte hw (retry_a_native_ready family ht hw hd tile hp p part)
  | b p part => exact Unified.tma_ready_writer_byte hw (retry_b_native_ready family ht hw hd tile hp p part)

theorem completed_candidate_retry_native_publication {tiles initial candidate} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) :
    ∃ family : ReplySourceFamily tiles candidate, ∀ tile, tile < tiles → ∀ operand,
      Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate (retryHistories family) dataCluster
        (retryNativeLocation family tile operand) (retryNativeProducer family tile operand) (retryNativeRead family tile operand) ∧
      ∃ value, Unified.writeByte Tma.localShared Access.globalDescriptor candidate (retryNativeProducer family tile operand)
        (retryNativeLocation family tile operand) = some value := by
  obtain ⟨family⟩ := completed_candidate_reply_family ht hb hw hc
  exact ⟨family,fun tile hp operand => ⟨retry_native_byte_order family ht hw hd tile hp operand,
    retry_native_producer_present family ht hw hd tile hp operand⟩⟩

end
end Ptx.Kernels.HopperDoubleBuffer
