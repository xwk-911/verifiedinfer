import Ptx.Kernels.HopperDoubleBufferRetryDataTensor
import Ptx.Kernels.HopperDoubleBufferRetryUnifiedControl

/-! Independently represented global inputs agree with every actual retry TMA
payload and the source tensor calls. These joint TMA/control/tensor components
do not yet select or admit a complete memory RF/co execution. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_data_copy_a_query (a b tiles schedules tile) :
    (replyCopyA tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).queryBase = retryDataCopyQuery tiles schedules tile 0 := by
  cases tile with
  | zero => rfl
  | succ tile =>
    change (replyPrefetchState tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).base.scalar.core.queries = _
    rw [reply_prefetch_queries]
    rfl

theorem retry_data_copy_b_query (a b tiles schedules tile) :
    (replyCopyB tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).queryBase = retryDataCopyQuery tiles schedules tile 1 := by
  cases tile with
  | zero => rfl
  | succ tile =>
    change (replyPrefetchState tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).base.scalar.core.queries+2 = _
    rw [reply_prefetch_queries]
    rfl

theorem retry_data_copy_a_fields (a b tiles schedules tile) (ht : tile < tiles) :
    (replyCopyA tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).descriptor = aView 65536 tiles ∧
      (replyCopyA tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).payload = HopperStage.aPayload (a tile) := by
  have hd : (replyCopyA tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).descriptor =
      (retryDataOracle a b tiles schedules 0).base.descriptor (replyCopyA tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).queryBase := by cases tile <;> rfl
  have hp : (replyCopyA tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).payload =
      (retryDataOracle a b tiles schedules 0).base.tmaBytes ((replyCopyA tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).queryBase+1) := by cases tile <;> rfl
  rw [hd,hp,retry_data_copy_a_query]
  exact ⟨retry_data_descriptor_a tiles schedules tile ht,retry_data_payload_a a b tiles schedules tile ht⟩

theorem retry_data_copy_b_fields (a b tiles schedules tile) (ht : tile < tiles) :
    (replyCopyB tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).descriptor = bView (dataBBase tiles) tiles ∧
      (replyCopyB tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).payload = HopperStage.bPayload (b tile) := by
  have hd : (replyCopyB tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).descriptor =
      (retryDataOracle a b tiles schedules 0).base.descriptor (replyCopyB tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).queryBase := by cases tile <;> rfl
  have hp : (replyCopyB tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).payload =
      (retryDataOracle a b tiles schedules 0).base.tmaBytes ((replyCopyB tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).queryBase+1) := by
    cases tile <;> simp only [replyCopyB,replyInitialB,prefetchBCopy,Nat.add_assoc]
  rw [hd,hp,retry_data_copy_b_query]
  exact ⟨retry_data_descriptor_b tiles schedules tile,retry_data_payload_b a b tiles schedules tile ht⟩

theorem retry_data_descriptors (a b tiles schedules) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Tma.DescriptorAgreement (retryDataCandidate a b tiles schedules).view (dataMaps tiles) := by
  intro id copy he
  obtain ⟨tile,hi,ha | hb'⟩ := retry_all_source_copies (retryDataFamily a b tiles schedules) ht
    (retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb) id copy he
  · rw [ha.2]
    dsimp only [retryDataFamily]
    rw [reply_copy_a_descriptor_address,(retry_data_copy_a_fields a b tiles schedules tile hi).1]
    rfl
  · rw [hb'.2]
    dsimp only [retryDataFamily]
    rw [reply_copy_b_descriptor_address,(retry_data_copy_b_fields a b tiles schedules tile hi).1]
    rfl

theorem retry_data_payload_agreement (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Tma.PayloadAgreement (retryDataCandidate a b tiles schedules).view (dataRepresentedInitial a b tiles frame) := by
  intro id copy he offset ho
  obtain ⟨tile,hi,ha | hb'⟩ := retry_all_source_copies (retryDataFamily a b tiles schedules) ht
    (retry_data_source a b tiles schedules (dataRepresentedInitial a b tiles frame) ht hb) id copy he
  · rw [ha.2] at ho ⊢
    dsimp only [retryDataFamily] at ho ⊢
    change offset < (replyCopyA tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).descriptor.bytes at ho
    have hf := retry_data_copy_a_fields a b tiles schedules tile hi
    rw [hf.1] at ho
    rw [hf.1,hf.2,reply_copy_a_coordinates tiles _ _ tile hb hi]
    exact data_copy_a_payload a b tiles tile frame hi ⟨offset,ho⟩
  · rw [hb'.2] at ho ⊢
    dsimp only [retryDataFamily] at ho ⊢
    change offset < (replyCopyB tiles (retryDataOracle a b tiles schedules 0) (schedules 0) tile).descriptor.bytes at ho
    have hf := retry_data_copy_b_fields a b tiles schedules tile hi
    rw [hf.1] at ho
    rw [hf.1,hf.2,reply_copy_b_coordinates tiles _ _ tile hb hi]
    exact data_copy_b_payload a b tiles tile frame hi ⟨offset,ho⟩

theorem retry_data_tma_components (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame))
      (retryDataCandidate a b tiles schedules) Tma.localShared (dataMaps tiles) (retryHistories (retryDataFamily a b tiles schedules)) :=
  retry_tma_components (retryDataFamily a b tiles schedules) ht (retry_data_source a b tiles schedules _ ht hb)
    (retry_data_complete a b tiles schedules ht hb) (retry_data_descriptors a b tiles schedules ht hb)
    (retry_data_payload_agreement a b tiles schedules frame ht hb)

theorem retry_data_tma_control_tensor_components (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame))
      (retryDataCandidate a b tiles schedules) Tma.localShared (dataMaps tiles) (retryHistories (retryDataFamily a b tiles schedules)) ∧
    Unified.ControlAdmitted HopperStage.block (retryDataCandidate a b tiles schedules) (retryHistories (retryDataFamily a b tiles schedules)) ∧
    ∀ tile < tiles, Wgmma.TensorConditions .zero ((retryDataFamily a b tiles schedules).calls tile) (dataSharedTile a b tile) :=
  ⟨retry_data_tma_components a b tiles schedules frame ht hb,
    retry_control_admitted (retryDataFamily a b tiles schedules) ht hb (retry_data_source a b tiles schedules (dataRepresentedInitial a b tiles frame) ht hb),
    fun tile hi => retry_data_tensor_component a b tiles schedules tile hi⟩

end
end Ptx.Kernels.HopperDoubleBuffer
