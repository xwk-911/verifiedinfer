import Ptx.Kernels.HopperDoubleBufferRetryTensorInputs

/-! Accumulation for actual source calls with arbitrary finite lane/tile retry
schedules. The fixed instruction's existing TensorConditions remain an explicit
semantic component. Memory identifies its inputs; induction derives the kernel
result. This is not full control, observer or execution-existence admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem reply_call_input_checkpoint (tiles lane reply retries tile slot) :
    (replyCall tiles lane reply retries tile).input slot =
      (replyTileCheckpoint tiles lane reply retries tile).2 slot := rfl

theorem reply_call_output_checkpoint (tiles lane reply retries tile slot) :
    (replyCall tiles lane reply retries tile).output slot =
      (replyTileCheckpoint tiles lane reply retries (tile+1)).2 slot := by
  simp only [replyTileCheckpoint,loopCheckpoint,Nat.zero_add]
  rfl

theorem reply_checkpoint_accumulation (tiles : Nat) (replies : Wgmma.Lane → Wgmma.Oracle)
    (schedules : Wgmma.Lane → Nat → Nat) (a : TileA) (b : TileB)
    (ha : ∀ tile, tile < tiles → Wgmma.Arithmetic (a tile) (b tile)
      (fun p => (replyCall tiles p.1 (replies p.1) (schedules p.1) tile).input p.2)
      (fun p => (replyCall tiles p.1 (replies p.1) (schedules p.1) tile).output p.2))
    (tile : Nat) (ht : tile ≤ tiles) (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    (replyTileCheckpoint tiles lane (replies lane) (schedules lane) tile).2 slot =
      result a b tile (Wgmma.cCoord (lane,slot)) := by
  induction tile generalizing lane slot with
  | zero => rfl
  | succ tile ih =>
    have hin : (fun p => (replyCall tiles p.1 (replies p.1) (schedules p.1) tile).input p.2) =
        Wgmma.gatherC (result a b tile) := by
      funext p
      rw [reply_call_input_checkpoint]
      exact ih (by omega) p.1 p.2
    rw [← reply_call_output_checkpoint]
    have hh := ha tile (by omega) (lane,slot)
    rw [hin] at hh
    simpa only [Wgmma.results,Wgmma.scatter_gather_c,Wgmma.gatherC,result] using hh

theorem reply_final_accumulation (tiles : Nat) (replies : Wgmma.Lane → Wgmma.Oracle)
    (schedules : Wgmma.Lane → Nat → Nat) (a : TileA) (b : TileB)
    (ha : ∀ tile, tile < tiles → Wgmma.Arithmetic (a tile) (b tile)
      (fun p => (replyCall tiles p.1 (replies p.1) (schedules p.1) tile).input p.2)
      (fun p => (replyCall tiles p.1 (replies p.1) (schedules p.1) tile).output p.2))
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    (replyCheckpoint tiles lane (replies lane) (schedules lane)).2 slot =
      specification a b tiles (Wgmma.cCoord (lane,slot)) := by
  exact (reply_checkpoint_accumulation tiles replies schedules a b ha tiles (Nat.le_refl _) lane slot).trans
    (result_matches_specification a b tiles _)

theorem retry_arithmetic_from_memory {a b tiles frame candidate initial rf co} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (retryHistories family) dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame) (tile : Nat) (ht : tile < tiles)
    (tensor : ∃ memory, Wgmma.TensorConditions .zero (family.calls tile) memory) :
    Wgmma.Arithmetic (a tile) (b tile) (fun p => (family.calls tile p.1).input p.2)
      (fun p => (family.calls tile p.1).output p.2) := by
  obtain ⟨memory,tensor⟩ := tensor
  exact (Unified.collective_arithmetic_inputs_identified (familyCollective family hw tile ht)
    (retry_tensor_inputs_from_memory family hw hc hd hb hm hi tile ht)
    (retry_call_storage family a b tile) tensor.tensor).2

theorem retry_final_accumulation_from_memory {a b tiles frame candidate initial rf co} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (retryHistories family) dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame)
    (tensor : ∀ tile, tile < tiles → ∃ memory, Wgmma.TensorConditions .zero (family.calls tile) memory)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    (replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).2 slot =
      specification a b tiles (Wgmma.cCoord (lane,slot)) := by
  apply reply_final_accumulation tiles family.replies family.schedules a b
  intro tile ht
  exact retry_arithmetic_from_memory family hw hc hd hb hm hi tile ht (tensor tile ht)

theorem retry_output_stores_from_memory {a b tiles frame candidate initial rf co} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (retryHistories family) dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame)
    (tensor : ∀ tile, tile < tiles → ∃ memory, Wgmma.TensorConditions .zero (family.calls tile) memory)
    (lane : Wgmma.Lane) :
    ((family.traces lane).events.filterMap globalWrite) = List.ofFn (fun slot : Wgmma.Slot =>
      (outputWordAddress (lane,slot),Symbolic.encode .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))))) := by
  rw [family.events,reply_positive_write_inventory]
  congr 1
  funext slot
  rw [retry_final_accumulation_from_memory family hw hc hd hb hm hi tensor]

end
end Ptx.Kernels.HopperDoubleBuffer
