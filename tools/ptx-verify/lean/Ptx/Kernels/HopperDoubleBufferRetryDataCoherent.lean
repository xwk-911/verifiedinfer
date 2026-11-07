import Ptx.Kernels.HopperDoubleBufferRetryDataCausal
import Ptx.Kernels.HopperDoubleBufferRetryStoreInventory
import Ptx.Hopper.UnifiedRankedCoherence

/-! Coherence from actual ordered shared writers and unique global writers.
Shared slot reuse is retained; uniqueness is used only for global outputs. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_shared_writers_order {tiles initial candidate loc left right lv rv} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hs : loc.space = .shared .zero)
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor candidate left loc = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor candidate right loc = some rv) :
    left = right ∨ Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate (retryHistories family) dataCluster loc left right ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor candidate (retryHistories family) dataCluster loc right left := by
  obtain ⟨id,offset,rfl,hloc⟩ := candidate_shared_writer_is_tensor hb hw hc hs hl
  obtain ⟨tile,hi,hregion⟩ := retry_tensor_write_region family ht hw hd hloc
  rcases hregion with ⟨_,ho,hbase⟩ | ⟨_,ho,hbase⟩
  · let owner := Wgmma.aByteOwner ⟨offset,ho⟩
    have hnative : retryNativeLocation family tile (.a owner.1 owner.2) = loc := by
      rw [retry_native_a_location]
      change (⟨.shared .zero,aBase (stage tile)+(Wgmma.aOffset (Wgmma.aByteOwner ⟨offset,ho⟩)).val⟩ : Location) = loc
      rw [Wgmma.a_offset_owner]
      exact hbase.symm
    have ho := retry_native_writers_comparable (tile := tile) (operand := .a owner.1 owner.2) family ht hw hc hd hb
      (by rw [hnative]; exact hl) (by rw [hnative]; exact hr)
    rwa [hnative] at ho
  · let owner := Wgmma.bByteOwner ⟨offset,ho⟩
    have hnative : retryNativeLocation family tile (.b owner.1 owner.2) = loc := by
      rw [retry_native_b_location]
      change (⟨.shared .zero,bBase (stage tile)+(Wgmma.bOffset (Wgmma.bByteOwner ⟨offset,ho⟩)).val⟩ : Location) = loc
      rw [Wgmma.b_offset_owner]
      exact hbase.symm
    have ho := retry_native_writers_comparable (tile := tile) (operand := .b owner.1 owner.2) family ht hw hc hd hb
      (by rw [hnative]; exact hl) (by rw [hnative]; exact hr)
    rwa [hnative] at ho

theorem retry_data_all_writers_order {a b tiles schedules loc left right lv rv} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) left loc = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) right loc = some rv) :
    left = right ∨ Unified.ByteOrder Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster loc left right ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
        (retryHistories (retryDataFamily a b tiles schedules)) dataCluster loc right left := by
  have hw := retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb
  have hc := retry_data_complete a b tiles schedules ht hb
  obtain ⟨base,size,hf,hs | hg⟩ := candidate_write_footprint_regions hb hw hc hl
  all_goals have hbound := Unified.access_footprint_bounds (.inr (by rw [hl]; rfl)) hf
  · exact retry_shared_writers_order (retryDataFamily a b tiles schedules) ht hb hw hc
      (retry_data_descriptors a b tiles schedules ht hb) (hbound.1.symm.trans hs.1) hl hr
  · exact .inl (retry_global_unique_writers (retryDataFamily a b tiles schedules) hb hw hc (hbound.1.symm.trans hg.1) hl hr)

theorem retry_data_coherent_witness (a b tiles schedules) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.Coherent Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster (retryDataReadWitness a b tiles schedules) (retryDataCoherenceWitness a b tiles schedules) := by
  apply Unified.ranked_coherent_of_write_order (retryDataMemoryRank a b tiles schedules)
  · intro loc left right ho
    exact retry_data_memory_byte_order_rank ht hb ho
  · intro loc left right lv rv hl hr hc
    exact retry_data_memory_causality_rank ht hb hc
  · intro loc left right lv rv hl hr
    exact retry_data_all_writers_order ht hb hl hr

end
end Ptx.Kernels.HopperDoubleBuffer
