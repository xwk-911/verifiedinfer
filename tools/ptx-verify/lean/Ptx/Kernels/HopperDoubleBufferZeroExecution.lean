import Ptx.Kernels.HopperDoubleBufferZeroMemory

/-! Universal completed zero-K components and observer refinement. No reads,
TMA or native collectives occur, but all real output stores and observer
coverage/finality remain checked. Initial bytes and source oracles are arbitrary. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def zeroStoreId := dataStoreId (fun _ _ => 0) (fun _ _ => 0) 0
def zeroOutputSelect := dataOutputSelect (fun _ _ => 0) (fun _ _ => 0) 0
def zeroObservation (candidate : Unified.Candidate) (initial : Location → Symbolic.Byte) : Unified.Observation :=
  Unified.selectedObservation Tma.localShared Access.globalDescriptor candidate (fun _ => initial) zeroOutputSelect dataOutputDomain

theorem completed_zero_output_byte {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    Unified.writeByte Tma.localShared Access.globalDescriptor candidate (.base (.tma (.source (zeroStoreId lane slot))))
      ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 0 index.val) := by
  rw [Unified.write_byte_lookup_eq (completed_zero_event_lookup hw hc)]
  simpa only [zeroCandidate,zeroStoreId,specification,Finset.range_zero,Finset.sum_empty] using data_actual_output_byte (fun _ _ => 0) (fun _ _ => 0) 0 lane slot index

theorem completed_zero_output_selection {initial candidate writer loc value}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) (hg : loc.space = .global)
    (he : Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer loc = some value) : zeroOutputSelect loc = some writer := by
  rw [Unified.write_byte_lookup_eq (completed_zero_event_lookup hw hc)] at he
  exact data_output_selection (a := fun _ _ => 0) (b := fun _ _ => 0) (tiles := 0) (by decide) hg he

theorem completed_zero_observer_eligible {initial candidate histories cluster rf}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) (loc : Location) (hg : loc.space = .global) :
    Unified.ObserverEligible Tma.localShared Access.globalDescriptor candidate histories cluster rf loc := by
  refine ⟨candidate_no_mixed_size_race (by decide) hw hc (completed_zero_descriptors hw hc),?_⟩
  rintro ⟨left,right,hl,hr,hrace⟩
  obtain ⟨vl,hvl⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨vr,hvr⟩ := Option.isSome_iff_exists.mp hr
  have he := completed_zero_global_writers_unique hw hc hg hvl hvr
  subst right
  exact hrace.notStrong (Unified.write_self_strong hvl)

theorem completed_zero_observer_witness {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate (fun _ => initial) zeroRf (zeroCo candidate)
      zeroHistories dataCluster (zeroObservation candidate initial) := by
  apply Unified.selected_observer hc
  · intro loc hl
    exact (mem_data_output_domain.mp hl).1
  · intro writer loc value hg hwrite
    have hb := candidate_global_write_bounds (by decide) hw hc hg hwrite
    exact mem_data_output_domain.mpr ⟨hg,by omega,by omega⟩
  · intro loc hl writer value hwrite
    exact completed_zero_output_selection hw hc (mem_data_output_domain.mp hl).1 hwrite
  · exact (completed_zero_coherent hw hc).irrefl

theorem completed_zero_observed_output_of_admission {initial candidate proxyInitial rf co histories cluster obs}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor candidate proxyInitial rf co histories cluster)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate proxyInitial rf co histories cluster obs)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = .realPart .f32 0 index.val := by
  have hwrite := completed_zero_output_byte hw hc lane slot index
  exact Unified.observer_unique_writer hm ho (ho.coverage _ _ _ rfl hwrite)
    (completed_zero_observer_eligible hw hc _ rfl) hwrite (fun _ _ hother => completed_zero_global_writers_unique hw hc rfl hother hwrite)

theorem completed_zero_observed_frame_of_admission {initial candidate proxyInitial rf co histories cluster obs loc}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate proxyInitial rf co histories cluster obs)
    (hd : loc ∈ obs.domain) (hg : loc.space = .global) (hout : ¬(8192 ≤ loc.address ∧ loc.address < 10240)) : obs.output loc = proxyInitial .generic loc :=
  Unified.observer_unwritten ho hd (completed_zero_observer_eligible hw hc loc hg) (candidate_global_outside_output_immutable (by decide) hw hc hg hout)

theorem completed_zero_observed_output {initial candidate obs}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate (fun _ => initial) zeroRf (zeroCo candidate) zeroHistories dataCluster obs)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    obs.output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = .realPart .f32 0 index.val := by
  exact completed_zero_observed_output_of_admission hw hc (completed_zero_memory_witness hw hc).toCausalConstraints ho lane slot index

theorem completed_zero_observed_frame {initial candidate obs loc}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate (fun _ => initial) zeroRf (zeroCo candidate) zeroHistories dataCluster obs)
    (hd : loc ∈ obs.domain) (hg : loc.space = .global) (hout : ¬(8192 ≤ loc.address ∧ loc.address < 10240)) : obs.output loc = initial loc :=
  Unified.observer_unwritten ho hd (completed_zero_observer_eligible hw hc loc hg) (candidate_global_outside_output_immutable (by decide) hw hc hg hout)

theorem completed_zero_components {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    Unified.TmaComponents code (completeLaunch 0 initial) candidate Tma.localShared (dataMaps 0) zeroHistories ∧
    Unified.ControlAdmitted HopperStage.block candidate zeroHistories ∧
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate (fun _ => initial) zeroRf (zeroCo candidate) zeroHistories dataCluster ∧
    (∀ id, candidate.representativeAt id = none) ∧
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate (fun _ => initial) zeroRf (zeroCo candidate) zeroHistories dataCluster (zeroObservation candidate initial) :=
  ⟨completed_zero_tma_components hw hc,completed_zero_control_admitted hw hc,completed_zero_memory_witness hw hc,
    completed_zero_representative_none hw hc,completed_zero_observer_witness hw hc⟩

theorem zero_execution_exists (initial : Location → Symbolic.Byte) :
    ∃ candidate : Unified.Candidate,
      Unified.TmaComponents code (completeLaunch 0 initial) candidate Tma.localShared (dataMaps 0) zeroHistories ∧
      Unified.ControlAdmitted HopperStage.block candidate zeroHistories ∧
      Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate (fun _ => initial) zeroRf (zeroCo candidate) zeroHistories dataCluster ∧
      Unified.ObserverConditions Tma.localShared Access.globalDescriptor candidate (fun _ => initial) zeroRf (zeroCo candidate) zeroHistories dataCluster (zeroObservation candidate initial) ∧
      ∀ lane slot (index : Fin 4), (zeroObservation candidate initial).output ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = .realPart .f32 0 index.val := by
  have hw : Unified.WellFormed code (completeLaunch 0 initial) zeroCandidate := data_source_well_formed _ _ 0 initial (by decide)
  have hc : Unified.Complete zeroCandidate := data_candidate_local _ _ 0 (by decide)
  obtain ⟨htma,hcontrol,hmemory,_,hobserver⟩ := completed_zero_components hw hc
  exact ⟨zeroCandidate,htma,hcontrol,hmemory,hobserver,completed_zero_observed_output hw hc hobserver⟩

end
end Ptx.Kernels.HopperDoubleBuffer
