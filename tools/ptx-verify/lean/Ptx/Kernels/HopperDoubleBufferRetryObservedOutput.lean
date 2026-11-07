import Ptx.Kernels.HopperDoubleBufferRetryStoreInventory
import Ptx.Kernels.HopperDoubleBufferObservedOutput

/-! Completed generic-proxy observation for actual arbitrary-retry source
families. Source ownership derives global writer uniqueness and eligibility.
Functional results retain the existing memory and instruction-arithmetic
components; full control/execution existence and physical observers are separate.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryOutputSelect {tiles candidate} (family : ReplySourceFamily tiles candidate) (loc : Location) : Option Unified.Node :=
  if loc.space = .global ∧ 8192 ≤ loc.address ∧ loc.address < 10240 then
    some (.base (.tma (.source (family.storeId (dataOutputOwner loc.address).1 (dataOutputOwner loc.address).2))))
  else none
def retryObservation {tiles candidate} (family : ReplySourceFamily tiles candidate) (initial : Unified.ProxyMemory) : Unified.Observation :=
  Unified.selectedObservation Tma.localShared Access.globalDescriptor candidate initial (retryOutputSelect family) dataOutputDomain

theorem retry_global_observer_eligible {tiles sourceInitial candidate histories cluster rf} (family : ReplySourceFamily tiles candidate)
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (loc : Location) (hg : loc.space = .global) :
    Unified.ObserverEligible Tma.localShared Access.globalDescriptor candidate histories cluster rf loc := by
  refine ⟨candidate_no_mixed_size_race hb hw hc hd,?_⟩
  rintro ⟨left,right,hl,hr,hrace⟩
  obtain ⟨vl,hvl⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨vr,hvr⟩ := Option.isSome_iff_exists.mp hr
  have he := retry_global_unique_writers family hb hw hc hg hvl hvr
  subst right
  exact hrace.notStrong (Unified.write_self_strong hvl)

theorem retry_output_selection {tiles sourceInitial candidate writer loc value} (family : ReplySourceFamily tiles candidate)
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (hg : loc.space = .global) (hwrite : Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer loc = some value) :
    retryOutputSelect family loc = some writer := by
  obtain ⟨lane,slot,rfl,hbounds⟩ := retry_global_writer_metadata family hb hw hc hg hwrite
  have hr := data_output_word_bounds lane slot
  have hloc : loc.space = .global ∧ 8192 ≤ loc.address ∧ loc.address < 10240 := ⟨hg,by omega,by omega⟩
  simp only [retryOutputSelect,ite_eq_left hloc,data_output_owner_byte hbounds]

theorem retry_selected_output_byte {tiles sourceInitial candidate initial} (family : ReplySourceFamily tiles candidate)
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (retryObservation family initial).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 ((replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).2 slot) index.val := by
  have hwrite := retry_actual_output_byte family hw lane slot index
  have hselect := retry_output_selection family hb hw hc rfl hwrite
  simp only [retryObservation,Unified.selectedObservation,hselect,hwrite,Option.getD_some]

theorem retry_observer_component {tiles sourceInitial candidate initial rf co histories cluster} (family : ReplySourceFamily tiles candidate)
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (hirr : ∀ loc source, ¬co loc source source) :
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories cluster (retryObservation family initial) := by
  apply Unified.selected_observer hc
  · intro loc hl; exact (mem_data_output_domain.mp hl).1
  · intro writer loc value hg hwrite
    obtain ⟨lane,slot,_,hl⟩ := retry_global_writer_metadata family hb hw hc hg hwrite
    have hr := data_output_word_bounds lane slot
    exact mem_data_output_domain.mpr ⟨hg,by omega,by omega⟩
  · intro loc hl writer value hwrite
    exact retry_output_selection family hb hw hc (mem_data_output_domain.mp hl).1 hwrite
  · exact hirr

theorem retry_observer_from_memory {tiles sourceInitial candidate initial rf co histories cluster} (family : ReplySourceFamily tiles candidate)
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories cluster) :
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories cluster (retryObservation family initial) :=
  retry_observer_component family hb hw hc (hm.coherence (candidate_no_mixed_size_race hb hw hc hd)).irrefl

theorem retry_observed_output_byte {tiles sourceInitial candidate initial rf co histories cluster obs} (family : ReplySourceFamily tiles candidate)
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hcausal : Unified.CausalConstraints Tma.localShared Access.globalDescriptor candidate initial rf co histories cluster)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories cluster obs)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 ((replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).2 slot) index.val := by
  have hwrite := retry_actual_output_byte family hw lane slot index
  exact Unified.observer_unique_writer hcausal ho (ho.coverage _ _ _ rfl hwrite)
    (retry_global_observer_eligible family hb hw hc hd _ rfl) hwrite
    (fun _ _ hother => retry_global_unique_writers family hb hw hc rfl hother hwrite)

theorem retry_observed_frame {tiles sourceInitial candidate initial rf co histories cluster obs loc} (family : ReplySourceFamily tiles candidate)
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate initial rf co histories cluster obs)
    (hdom : loc ∈ obs.domain) (hg : loc.space = .global) (hout : ¬(8192 ≤ loc.address ∧ loc.address < 10240)) :
    obs.output loc = initial .generic loc :=
  Unified.observer_unwritten ho hdom (retry_global_observer_eligible family hb hw hc hd loc hg)
    (candidate_global_outside_output_immutable hb hw hc hg hout)

theorem retry_observed_matrix_byte {a b tiles frame candidate initial rf co obs} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (retryHistories family) dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame)
    (tensor : ∀ tile, tile < tiles → ∃ memory, Wgmma.TensorConditions .zero (family.calls tile) memory)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate initial rf co (retryHistories family) dataCluster obs)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val := by
  rw [retry_observed_output_byte family hb hw hc hd hm.toCausalConstraints ho,
    retry_final_accumulation_from_memory family hw hc hd hb hm hi tensor]

theorem retry_selected_observed_matrix {a b tiles frame candidate initial rf co} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (retryHistories family) dataCluster)
    (hi : initial = fun _ => dataRepresentedInitial a b tiles frame)
    (tensor : ∀ tile, tile < tiles → ∃ memory, Wgmma.TensorConditions .zero (family.calls tile) memory)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (retryObservation family initial).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      .realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val :=
  retry_observed_matrix_byte family hw hc hd hb hm hi tensor (retry_observer_from_memory family hb hw hc hd hm) lane slot index

end
end Ptx.Kernels.HopperDoubleBuffer
