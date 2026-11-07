import Ptx.Kernels.HopperDoubleBufferRetryObservedOutput
import Ptx.Tests.HopperRetryAdmission

/-! Actual source writers and positive completed-observer components for the
nonzero heterogeneous-retry fixture. Its memory conditions remain refuted by
the bits/realPart mismatch: neither selected observation nor initialization-
only coherence is used as a positive full memory/control execution witness. -/
namespace Ptx.HopperRetryObservedOutputTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev family := HopperRetryAdmissionTests.family
abbrev candidate := HopperRetryAdmissionTests.candidate
abbrev source := HopperRetryAdmissionTests.source_well_formed
abbrev complete := HopperRetryAdmissionTests.source_complete
abbrev descriptors := HopperRetryAdmissionTests.actual_descriptor_admission
def initial : Unified.ProxyMemory := fun _ _ => .bits (byte 17)
def co (value : ℝ) := Unified.InitialCo Tma.localShared Access.globalDescriptor (candidate value)
def observation (value : ℝ) := retryObservation (family value) initial

theorem actual_store_indices (value : ℝ) :
    ((family value).storeId 0 0).serial = 41 ∧ ((family value).storeId 0 3).serial = 44 ∧
    ((family value).storeId 2 0).serial = 35 ∧ ((family value).storeId 2 3).serial = 38 := ⟨rfl,rfl,rfl,rfl⟩

theorem actual_output_bytes (value : ℝ) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value)
      (.base (.tma (.source ((family value).storeId lane slot))))
      ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 value index.val) :=
  retry_actual_output_byte (family value) (source value (fun _ => .bits (byte 0))) lane slot index

theorem global_writers_unique (value : ℝ) (loc : Location) (hg : loc.space = .global) (left right : Unified.Node) (lv rv : Symbolic.Byte)
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value) left loc = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value) right loc = some rv) : left = right :=
  retry_global_unique_writers (family value) (by decide) (source value (fun _ => .bits (byte 0))) (complete value) hg hl hr

theorem arbitrary_global_observer_eligible (value : ℝ) (histories : Location → List Tma.Entry) (cluster : Unified.ClusterScope)
    (rf : Unified.ReadsFrom) (loc : Location) (hg : loc.space = .global) :
    Unified.ObserverEligible Tma.localShared Access.globalDescriptor (candidate value) histories cluster rf loc :=
  retry_global_observer_eligible (family value) (by decide) (source value (fun _ => .bits (byte 0))) (complete value) (descriptors value) loc hg

theorem completed_observer_component (value : ℝ) (rf : Unified.ReadsFrom) :
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate value) initial rf (co value)
      (retryHistories (family value)) dataCluster (observation value) := by
  apply retry_observer_component (family value) (by decide) (source value (fun _ => .bits (byte 0))) (complete value)
  rintro loc a ⟨hl,writer,hr,_⟩
  have he : (none : Option Unified.Node) = some writer := hl.symm.trans hr
  cases he

theorem selected_actual_output (value : ℝ) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (observation value).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = .realPart .f32 value index.val :=
  retry_selected_output_byte (family value) (by decide) (source value (fun _ => .bits (byte 0))) (complete value) lane slot index

theorem adjacent_frame_preserved (value : ℝ) :
    (observation value).output ⟨.global,8191⟩ = .bits (byte 17) ∧
      (observation value).output ⟨.global,10240⟩ = .bits (byte 17) := by
  constructor
  · exact retry_observed_frame (family value) (by decide) (source value (fun _ => .bits (byte 0))) (complete value) (descriptors value)
      (completed_observer_component value (fun _ _ => none)) (mem_data_output_domain.mpr ⟨rfl,by decide,by decide⟩) rfl (by decide)
  · exact retry_observed_frame (family value) (by decide) (source value (fun _ => .bits (byte 0))) (complete value) (descriptors value)
      (completed_observer_component value (fun _ _ => none)) (mem_data_output_domain.mpr ⟨rfl,by decide,by decide⟩) rfl (by decide)

def omitted (value : ℝ) : Unified.Observation := {observation value with domain := []}
def stale (value : ℝ) : Unified.Observation := {observation value with source := fun _ => none,output := initial .generic}
def wrong : Unified.Observation := {observation 1 with output := fun _ => .realPart .f32 0 0}

theorem omitted_output_rejected (value : ℝ) (rf : Unified.ReadsFrom) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate value) initial rf (co value)
      (retryHistories (family value)) dataCluster (omitted value) := by
  intro ho
  have hh := ho.coverage _ _ _ rfl (actual_output_bytes value 0 0 0)
  cases hh

theorem stale_output_rejected (value : ℝ) (rf : Unified.ReadsFrom) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate value) initial rf (co value)
      (retryHistories (family value)) dataCluster (stale value) := by
  intro ho
  have hwrite := actual_output_bytes value 0 0 0
  have hdom := ho.coverage _ _ _ rfl hwrite
  have hh := ho.noStale _ hdom
    (candidate_no_mixed_size_race (by decide) (source value (fun _ => .bits (byte 0))) (complete value) (descriptors value)) _ _ hwrite
  apply hh
  refine ⟨rfl,_,rfl,?_⟩
  change (Unified.writeByte Tma.localShared Access.globalDescriptor (candidate value) _ _).isSome = true
  rw [hwrite]; rfl

theorem fabricated_observed_value_rejected (rf : Unified.ReadsFrom) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate 1) initial rf (co 1)
      (retryHistories (family 1)) dataCluster wrong := by
  intro ho
  have hwrite := actual_output_bytes 1 0 0 0
  simp only [Fin.val_zero] at hwrite
  have hdom := ho.coverage _ _ _ rfl hwrite
  have hv := ho.agreement _ hdom (arbitrary_global_observer_eligible 1 _ _ rf _ rfl)
  have hs : wrong.source ((⟨.global,outputWordAddress (0,0)⟩ : Location).add 0) =
      some (.base (.tma (.source ((family 1).storeId 0 0)))) := by
    have hselect := retry_output_selection (family 1) (by decide) (source 1 (fun _ => .bits (byte 0))) (complete 1) rfl hwrite
    simp only [wrong,observation,retryObservation,Unified.selectedObservation,hselect,hwrite,Option.isSome_some,ite_true]
  rw [hs,Unified.observerValue,hwrite] at hv
  change some (Symbolic.Byte.realPart .f32 (1 : ℝ) 0) = some (Symbolic.Byte.realPart .f32 (0 : ℝ) 0) at hv
  norm_num at hv

end
end Ptx.HopperRetryObservedOutputTests
