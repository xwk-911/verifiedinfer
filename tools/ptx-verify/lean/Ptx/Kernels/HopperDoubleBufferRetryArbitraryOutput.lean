import Ptx.Kernels.HopperDoubleBufferRetryPublicationTensor
import Ptx.Kernels.HopperDoubleBufferRetryObservedOutput

/-! Positive-K input and completed-observer refinement over arbitrary admitted
histories. Public entries derive publication from existing source/TMA/control
components. The existing tensor-instruction semantic component stays explicit;
no desired operands, RF choice or output value is assumed. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem arbitrary_history_native_reads_from_current {tiles sourceInitial candidate initial rf co} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles sourceInitial) candidate Tma.localShared (dataMaps tiles) histories)
    (hcomplete : Unified.Complete candidate) (hcontrol : Unified.ControlAdmitted HopperStage.block candidate histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster)
    (tile : Nat) (hlt : tile < tiles) (operand : Wgmma.OperandByte) :
    rf (retryNativeRead family tile operand) (retryNativeLocation family tile operand) = some (retryNativeProducer family tile operand) :=
  publication_native_reads_from_current family (arbitrary_native_publication_facts family ht htma hcontrol)
    htma.source hcomplete htma.descriptors hb hm tile hlt operand

theorem arbitrary_history_operand_byte {a b tiles frame candidate initial rf co} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate Tma.localShared (dataMaps tiles) histories)
    (hcomplete : Unified.Complete candidate) (hcontrol : Unified.ControlAdmitted HopperStage.block candidate histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame) (tile : Nat) (hlt : tile < tiles) (operand : Wgmma.OperandByte) :
    Unified.readByte Tma.localShared Access.globalDescriptor candidate (retryNativeRead family tile operand) (retryNativeLocation family tile operand) =
      some (dataSharedTile a b tile (retryNativeLocation family tile operand)) := by
  have hpub := arbitrary_native_publication_facts family ht htma hcontrol
  have hc := publication_native_current_write_value family hpub htma.source hcomplete htma.descriptors hb hm tile hlt operand
  have hv := retry_native_producer_storage family htma.source hcomplete htma.descriptors hb hm hi tile hlt operand
  have he := Option.some.inj (hc.symm.trans hv)
  rw [retry_native_read_byte family htma.source tile hlt operand,he]

theorem arbitrary_history_tensor_inputs {a b tiles frame candidate initial rf co} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate Tma.localShared (dataMaps tiles) histories)
    (hcomplete : Unified.Complete candidate) (hcontrol : Unified.ControlAdmitted HopperStage.block candidate histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame) (tile : Nat) (hlt : tile < tiles) :
    Wgmma.InputAgreement .zero (family.calls tile 0) (dataSharedTile a b tile) :=
  publication_tensor_inputs_from_memory family (arbitrary_native_publication_facts family ht htma hcontrol)
    htma.source hcomplete htma.descriptors hb hm hi tile hlt

theorem arbitrary_history_observed_matrix_byte {a b tiles frame candidate initial rf co obs} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate Tma.localShared (dataMaps tiles) histories)
    (hcomplete : Unified.Complete candidate) (hcontrol : Unified.ControlAdmitted HopperStage.block candidate histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame)
    (tensor : ∀ tile, tile < tiles → ∃ memory, Wgmma.TensorConditions .zero (family.calls tile) memory)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster obs)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val := by
  rw [retry_observed_output_byte family hb htma.source hcomplete htma.descriptors hm.toCausalConstraints ho,
    publication_final_accumulation_from_memory family (arbitrary_native_publication_facts family ht htma hcontrol)
      htma.source hcomplete htma.descriptors hb hm hi tensor]

theorem arbitrary_history_observed_gemm {a b tiles frame candidate initial rf co obs} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate Tma.localShared (dataMaps tiles) histories)
    (hcomplete : Unified.Complete candidate) (hcontrol : Unified.ControlAdmitted HopperStage.block candidate histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame)
    (tensor : ∀ tile, tile < tiles → ∃ memory, Wgmma.TensorConditions .zero (family.calls tile) memory)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster obs) :
    (∀ lane slot (index : Fin 4), obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val) ∧
    (∀ loc ∈ obs.domain, loc.space = .global → ¬(8192 ≤ loc.address ∧ loc.address < 10240) →
      obs.output loc = dataRepresentedInitial a b tiles frame loc) := by
  constructor
  · exact arbitrary_history_observed_matrix_byte family ht hb htma hcomplete hcontrol hm hi tensor ho
  · intro loc hdom hg hout
    have hframe := retry_observed_frame family hb htma.source hcomplete htma.descriptors ho hdom hg hout
    simpa only [hi] using hframe

theorem completed_candidate_arbitrary_gemm {a b tiles frame candidate initial rf co obs} {histories : Location → List Tma.Entry}
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate Tma.localShared (dataMaps tiles) histories)
    (hcomplete : Unified.Complete candidate) (hcontrol : Unified.ControlAdmitted HopperStage.block candidate histories)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster obs) :
    ∃ family : ReplySourceFamily tiles candidate,
      (∀ tile, tile < tiles → ∃ memory, Wgmma.TensorConditions .zero (family.calls tile) memory) →
      (∀ lane slot (index : Fin 4), obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
        .realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val) ∧
      (∀ loc ∈ obs.domain, loc.space = .global → ¬(8192 ≤ loc.address ∧ loc.address < 10240) →
        obs.output loc = dataRepresentedInitial a b tiles frame loc) := by
  obtain ⟨family⟩ := completed_candidate_reply_family ht hb htma.source hcomplete
  exact ⟨family,fun tensor => arbitrary_history_observed_gemm family ht hb htma hcomplete hcontrol hm hi tensor ho⟩

end
end Ptx.Kernels.HopperDoubleBuffer
