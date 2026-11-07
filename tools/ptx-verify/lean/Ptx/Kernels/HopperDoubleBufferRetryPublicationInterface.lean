import Ptx.Kernels.HopperDoubleBufferRetryArbitraryObservations
import Ptx.Kernels.HopperDoubleBufferRetryMemoryPhases

/-! A publication interface independent of the chosen resource history. Its
arbitrary-history implementation follows actual completion observations; the
constructed implementation retains the earlier regression proof. Reuse still
uses native completion, not mbarrier completion. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def NativePublicationFacts {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (histories : Location → List Tma.Entry) : Prop :=
  ∀ tile, tile < tiles → ∀ operand,
    Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate histories dataCluster
      (retryNativeLocation family tile operand) (retryNativeProducer family tile operand) (retryNativeRead family tile operand)

theorem constructed_native_publication_facts {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) : NativePublicationFacts family (retryHistories family) :=
  fun tile htile operand => retry_native_byte_order family ht hw hd tile htile operand

theorem arbitrary_history_a_native_ready {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) histories)
    (hc : Unified.ControlAdmitted HopperStage.block candidate histories) (tile : Nat) (hlt : tile < tiles) (p : Wgmma.ACoord) (part : Fin 2) :
    Unified.TmaReady Tma.localShared candidate histories dataCluster (family.copyAId tile) (Wgmma.aOffset (p,part)).val
      (family.mmaId tile 0) (.a p part) (Wgmma.operandLocation .zero (family.calls tile 0) (.a p part)) :=
  family_tma_ready_from_observation family htma.source tile hlt (retry_operand_a_transfer family htma.source htma.descriptors tile hlt 0 p part) rfl
    (arbitrary_history_completion_observed family ht htma.source htma.descriptors htma.histories_valid hc.2 true tile hlt)

theorem arbitrary_history_b_native_ready {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) histories)
    (hc : Unified.ControlAdmitted HopperStage.block candidate histories) (tile : Nat) (hlt : tile < tiles) (p : Wgmma.BCoord) (part : Fin 2) :
    Unified.TmaReady Tma.localShared candidate histories dataCluster (family.copyBId tile) (Wgmma.bOffset (p,part)).val
      (family.mmaId tile 0) (.b p part) (Wgmma.operandLocation .zero (family.calls tile 0) (.b p part)) :=
  family_tma_ready_from_observation family htma.source tile hlt (retry_operand_b_transfer family htma.source htma.descriptors tile hlt 0 p part) rfl
    (arbitrary_history_completion_observed family ht htma.source htma.descriptors htma.histories_valid hc.2 false tile hlt)

theorem arbitrary_history_native_publication {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) histories)
    (hc : Unified.ControlAdmitted HopperStage.block candidate histories) (tile : Nat) (hlt : tile < tiles) (operand : Wgmma.OperandByte) :
    Unified.NativePublished Tma.localShared candidate histories dataCluster
      (retryNativeLocation family tile operand) (retryNativeProducer family tile operand) (retryNativeRead family tile operand) := by
  cases operand with
  | a p part => exact arbitrary_history_a_native_ready family ht htma hc tile hlt p part
  | b p part => exact arbitrary_history_b_native_ready family ht htma hc tile hlt p part

theorem arbitrary_native_publication_facts {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) histories)
    (hc : Unified.ControlAdmitted HopperStage.block candidate histories) : NativePublicationFacts family histories :=
  fun tile htile operand => Unified.native_published_byte_order (arbitrary_history_native_publication family ht htma hc tile htile operand)

theorem history_native_reuse_byte_order {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (tile next : Nat) (hlt : tile < next) (hn : next < tiles) (hs : stage tile = stage next) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate histories dataCluster
      (retryNativeLocation family tile operand) (retryNativeRead family tile operand) (retryNativeProducer family next operand) :=
  Unified.native_reuse_byte_order (retry_native_reuse family hw hd hb tile next hlt hn hs operand)

end
end Ptx.Kernels.HopperDoubleBuffer
