import Ptx.Kernels.HopperDoubleBufferRetryMemoryInputs
import Ptx.Hopper.UnifiedTensorMemory

/-! Native input bytes identified with independently represented arbitrary
real global matrices through actual source copies and admitted memory RF.
No desired operand/matrix reply is assumed. Native arithmetic, global control
and fully admitted execution existence remain separate obligations. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem reply_copy_a_coordinates (tiles reply retries tile) (hb : tiles ≤ 2^28) (ht : tile < tiles) :
    (replyCopyA tiles reply retries tile).coordinates = ⟨0,(8*tile : Nat)⟩ := by
  cases tile with
  | zero => rfl
  | succ tile =>
    change (⟨0,Tma.signed32 (8*(tile+1))⟩ : Tma.Coordinates) = _
    rw [(source_coordinate_small ht hb).2.1]

theorem reply_copy_b_coordinates (tiles reply retries tile) (hb : tiles ≤ 2^28) (ht : tile < tiles) :
    (replyCopyB tiles reply retries tile).coordinates = ⟨0,(tile : Int)⟩ := by
  cases tile with
  | zero => rfl
  | succ tile =>
    change (⟨0,Tma.signed32 (tile+1)⟩ : Tma.Coordinates) = _
    rw [(source_coordinate_small ht hb).2.2]

theorem retry_copy_a_source_byte {tiles sourceInitial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28) (tile : Nat) (ht : tile < tiles) (offset : Fin 2048) :
    Tma.sourceByte (replyCopyA tiles (family.replies 0) (family.schedules 0) tile).descriptor
      (replyCopyA tiles (family.replies 0) (family.schedules 0) tile).coordinates offset.val =
        some ⟨.global,65536+2048*tile+offset.val⟩ := by
  rw [family_copy_a_descriptor family hw hd tile ht,reply_copy_a_coordinates tiles (family.replies 0) (family.schedules 0) tile hb ht]
  exact a_tile_source ht offset.isLt

theorem retry_copy_b_source_byte {tiles sourceInitial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28) (tile : Nat) (ht : tile < tiles) (offset : Fin 256) :
    Tma.sourceByte (replyCopyB tiles (family.replies 0) (family.schedules 0) tile).descriptor
      (replyCopyB tiles (family.replies 0) (family.schedules 0) tile).coordinates offset.val =
        some ⟨.global,dataBBase tiles+256*tile+offset.val⟩ := by
  rw [family_copy_b_descriptor family hw hd tile ht,reply_copy_b_coordinates tiles (family.replies 0) (family.schedules 0) tile hb ht]
  exact packed_slice_source_byte (dataBBase tiles) tiles 1 tile offset.val offset.isLt (by omega)

theorem retry_transfer_a_byte_from_memory {a b tiles frame candidate initial rf co} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame) (tile : Nat) (ht : tile < tiles) (offset : Fin 2048) :
    Tma.transferByte candidate.view (family.copyAId tile) offset.val =
      some (dataSharedTile a b tile ⟨.shared .zero,aBase (stage tile)+offset.val⟩) := by
  subst initial
  have hp := candidate_payload_from_descriptors hb hw hc hd hm.toCausalConstraints
  have ho : offset.val < (replyCopyA tiles (family.replies 0) (family.schedules 0) tile).descriptor.bytes := by
    rw [family_copy_a_descriptor family hw hd tile ht]
    exact offset.isLt
  have hv := hp _ _ (family_copy_a_at family hw tile ht) offset.val ho
  rw [Tma.transferByte,family_copy_a_at family hw tile ht]
  simp only [Option.bind_some]
  rw [hv,Tma.copied_byte (retry_copy_a_source_byte family hw hd hb tile ht offset),data_initial_a_byte a b tiles tile frame ht offset]
  simp only [dataSharedTile,Wgmma.tileMemory,ite_true,Nat.add_sub_cancel_left]

theorem retry_transfer_b_byte_from_memory {a b tiles frame candidate initial rf co} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame) (tile : Nat) (ht : tile < tiles) (offset : Fin 256) :
    Tma.transferByte candidate.view (family.copyBId tile) offset.val =
      some (dataSharedTile a b tile ⟨.shared .zero,bBase (stage tile)+offset.val⟩) := by
  subst initial
  have hp := candidate_payload_from_descriptors hb hw hc hd hm.toCausalConstraints
  have ho : offset.val < (replyCopyB tiles (family.replies 0) (family.schedules 0) tile).descriptor.bytes := by
    rw [family_copy_b_descriptor family hw hd tile ht]
    exact offset.isLt
  have hv := hp _ _ (family_copy_b_at family hw tile ht) offset.val ho
  rw [Tma.transferByte,family_copy_b_at family hw tile ht]
  simp only [Option.bind_some]
  rw [hv,Tma.copied_byte (retry_copy_b_source_byte family hw hd hb tile ht offset),data_initial_b_byte a b tiles tile frame ht offset]
  have hs : bBase (stage tile)+offset.val-aBase (stage tile) = 2048+offset.val := by dsimp [aBase,bBase]; omega
  simp only [dataSharedTile,Wgmma.tileMemory,ite_true,hs]

theorem retry_native_producer_storage {a b tiles frame candidate initial rf co} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame) (tile : Nat) (ht : tile < tiles) (operand : Wgmma.OperandByte) :
    Unified.writeByte Tma.localShared Access.globalDescriptor candidate (retryNativeProducer family tile operand) (retryNativeLocation family tile operand) =
      some (dataSharedTile a b tile (retryNativeLocation family tile operand)) := by
  cases operand with
  | a p part =>
    rw [retry_native_a_location]
    exact Access.tensor_write (descriptor := Access.globalDescriptor) (retry_transfer_a_location family hw hd tile ht _)
      (retry_transfer_a_byte_from_memory family hw hc hd hb hm hi tile ht (Wgmma.aOffset (p,part)))
  | b p part =>
    rw [retry_native_b_location]
    exact Access.tensor_write (descriptor := Access.globalDescriptor) (retry_transfer_b_location family hw hd tile ht _)
      (retry_transfer_b_byte_from_memory family hw hc hd hb hm hi tile ht (Wgmma.bOffset (p,part)))

theorem retry_call_storage {tiles candidate} (family : ReplySourceFamily tiles candidate) (a : TileA) (b : TileB) (tile : Nat) :
    Wgmma.MatrixStorage .zero (family.calls tile 0) (dataSharedTile a b tile) (a tile) (b tile) := by
  constructor
  · intro p part
    rw [show Wgmma.operandLocation .zero (family.calls tile 0) (.a p part) = _ from
      reply_operand_a_location tiles 0 (family.replies 0) (family.schedules 0) tile p part]
    simpa only [dataSharedTile,Wgmma.tileMemory,ite_true,Nat.add_sub_cancel_left] using Wgmma.tile_byte_a (a tile) (b tile) p part
  · intro p part
    rw [show Wgmma.operandLocation .zero (family.calls tile 0) (.b p part) = _ from
      reply_operand_b_location tiles 0 (family.replies 0) (family.schedules 0) tile p part]
    have hs : bBase (stage tile)+(Wgmma.bOffset (p,part)).val-aBase (stage tile) = 2048+(Wgmma.bOffset (p,part)).val := by dsimp [aBase,bBase]; omega
    simpa only [dataSharedTile,Wgmma.tileMemory,ite_true,hs] using Wgmma.tile_byte_b (a tile) (b tile) p part

theorem retry_tensor_inputs_from_memory {a b tiles frame candidate initial rf co} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (retryHistories family) dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame) (tile : Nat) (ht : tile < tiles) :
    Wgmma.InputAgreement .zero (family.calls tile 0) (dataSharedTile a b tile) :=
  Unified.collective_input_from_sources (familyCollective family hw tile ht) hm.toCausalConstraints
    (retryNativeProducer family tile) (retry_native_eligible family hw hc hd hb tile ht rf)
    (retry_native_reads_from_current family hw hc hd hb hm tile ht) (retry_native_producer_storage family hw hc hd hb hm hi tile ht)

end
end Ptx.Kernels.HopperDoubleBuffer
