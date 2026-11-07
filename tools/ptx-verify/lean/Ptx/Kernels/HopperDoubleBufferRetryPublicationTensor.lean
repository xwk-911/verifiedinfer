import Ptx.Kernels.HopperDoubleBufferRetryPublicationMemory
import Ptx.Kernels.HopperDoubleBufferRetryArithmetic

/-! Actual byte sources identify native inputs under the publication interface.
The existing fixed-instruction TensorConditions then establish arithmetic and
source accumulation; desired operand values are not an added oracle premise. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem publication_tensor_inputs_from_memory {a b tiles frame candidate initial rf co} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (hpub : NativePublicationFacts family histories)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame) (tile : Nat) (ht : tile < tiles) :
    Wgmma.InputAgreement .zero (family.calls tile 0) (dataSharedTile a b tile) :=
  Unified.collective_input_from_sources (familyCollective family hw tile ht) hm.toCausalConstraints
    (retryNativeProducer family tile) (publication_native_eligible family hpub hw hc hd hb tile ht rf)
    (publication_native_reads_from_current family hpub hw hc hd hb hm tile ht)
    (retry_native_producer_storage family hw hc hd hb hm hi tile ht)

theorem publication_arithmetic_from_memory {a b tiles frame candidate initial rf co} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate) (hpub : NativePublicationFacts family histories)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (histories) dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame) (tile : Nat) (ht : tile < tiles)
    (tensor : ∃ memory, Wgmma.TensorConditions .zero (family.calls tile) memory) :
    Wgmma.Arithmetic (a tile) (b tile) (fun p => (family.calls tile p.1).input p.2)
      (fun p => (family.calls tile p.1).output p.2) := by
  obtain ⟨memory,tensor⟩ := tensor
  exact (Unified.collective_arithmetic_inputs_identified (familyCollective family hw tile ht)
    (publication_tensor_inputs_from_memory family hpub hw hc hd hb hm hi tile ht)
    (retry_call_storage family a b tile) tensor.tensor).2

theorem publication_final_accumulation_from_memory {a b tiles frame candidate initial rf co} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate) (hpub : NativePublicationFacts family histories)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (histories) dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame)
    (tensor : ∀ tile, tile < tiles → ∃ memory, Wgmma.TensorConditions .zero (family.calls tile) memory)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    (replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).2 slot =
      specification a b tiles (Wgmma.cCoord (lane,slot)) := by
  apply reply_final_accumulation tiles family.replies family.schedules a b
  intro tile ht
  exact publication_arithmetic_from_memory family hpub hw hc hd hb hm hi tile ht (tensor tile ht)

theorem publication_output_stores_from_memory {a b tiles frame candidate initial rf co} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate) (hpub : NativePublicationFacts family histories)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (histories) dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame)
    (tensor : ∀ tile, tile < tiles → ∃ memory, Wgmma.TensorConditions .zero (family.calls tile) memory)
    (lane : Wgmma.Lane) :
    ((family.traces lane).events.filterMap globalWrite) = List.ofFn (fun slot : Wgmma.Slot =>
      (outputWordAddress (lane,slot),Symbolic.encode .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))))) := by
  rw [family.events,reply_positive_write_inventory]
  congr 1
  funext slot
  rw [publication_final_accumulation_from_memory family hpub hw hc hd hb hm hi tensor]


end
end Ptx.Kernels.HopperDoubleBuffer
