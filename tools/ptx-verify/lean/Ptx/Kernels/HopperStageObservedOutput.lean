import Ptx.Kernels.HopperStageObserverWitness

/-! Observed matrix and frame contracts on the actual source family, for any
compatible RF/co/observer. This is not arbitrary-source reconstruction or IEEE
equivalence. The independent bundle below has no memory-admission premise. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem actual_output_byte (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) (.base (.tma (.source (storeId lane slot))))
      ((⟨.global,wordAddress lane slot⟩ : Location).add index.val) =
      some (.realPart .f32 (Wgmma.matrixStep a b (fun _ => 0) (Wgmma.cCoord (lane,slot))) index.val) := by
  rw [wordAddress,actual_output_address]
  have he : Access.kind Tma.localShared Access.globalDescriptor (candidate a b).view (.tma (.source (storeId lane slot))) =
      some (.write ⟨.global,8192+4*(8*(Wgmma.cCoord (lane,slot)).1.val+(Wgmma.cCoord (lane,slot)).2.val)⟩
        (Symbolic.encode .f32 (Wgmma.matrixStep a b (fun _ => 0) (Wgmma.cCoord (lane,slot))))) := by
    simp only [Access.kind,Unified.view_eventAt,actual_candidate_store,Option.map_some,Unified.eventView,Option.bind_some]
  rw [Unified.base_write_preserved,Access.writeByte,he,Option.bind_some,Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte_offset]
  simp only [Symbolic.encode,Symbolic.Format.bytes,List.getElem?_map,List.getElem?_range index.isLt,Option.map_some]
theorem observed_matrix_byte {a b initial rf co obs}
    (hc : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate a b) initial rf co histories cluster)
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b) initial rf co histories cluster obs)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    obs.output ((⟨.global,wordAddress lane slot⟩ : Location).add index.val) =
      .realPart .f32 (Wgmma.matrixStep a b (fun _ => 0) (Wgmma.cCoord (lane,slot))) index.val := by
  have hw := actual_output_byte a b lane slot index
  exact Unified.observer_unique_writer hc ho (ho.coverage _ _ _ rfl hw) (stage_observer_eligible a b rf _) hw
    (fun _ _ hother => stage_unique_writers hother hw)
theorem observed_frame {a b initial rf co obs loc}
    (ho : Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b) initial rf co histories cluster obs)
    (hd : loc ∈ obs.domain) (hg : loc.space = .global) (hf : ¬(8192 ≤ loc.address ∧ loc.address < 10240)) :
    obs.output loc = initial .generic loc := by
  apply Unified.observer_unwritten ho hd (stage_observer_eligible a b rf loc)
  intro writer
  cases hw : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) writer loc with
  | none => rfl
  | some value =>
    obtain ⟨lane,slot,_,hb⟩ := global_writer_metadata hg hw
    have hh := word_address_bounds lane slot
    exact (hf ⟨by omega,by omega⟩).elim
theorem independent_observed_matrix (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    (observation a b frame).output ((⟨.global,wordAddress lane slot⟩ : Location).add index.val) =
      .realPart .f32 (Wgmma.matrixStep a b (fun _ => 0) (Wgmma.cCoord (lane,slot))) index.val :=
  observed_matrix_byte (stage_causal_witness a b frame) (stage_observer_witness a b frame) lane slot index
theorem independent_observed_frame (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte)
    (loc : Location) (hd : loc ∈ outputDomain) (hf : ¬(8192 ≤ loc.address ∧ loc.address < 10240)) :
    (observation a b frame).output loc = frame loc := by
  obtain ⟨hg,hlo,hhi⟩ := mem_output_domain.mp hd
  have he := observed_frame (stage_observer_witness a b frame) hd hg hf
  change (observation a b frame).output loc = representedInitial a b frame loc at he
  rw [initial_frame a b frame loc (by omega) (by omega) (by omega) (by omega)] at he
  exact he
theorem stage_independent_components (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) :
    Unified.TmaComponents Generated.hopper_gemm_stage.program (launch (representedInitial a b frame))
        (candidate a b) Tma.localShared maps histories ∧
    Unified.SchedulesAdmitted block (candidate a b) ∧
    Wgmma.TensorConditions .zero (calls a b) (transferView a b) ∧
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b)
      (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster ∧
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b)
      (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster (observation a b frame) :=
  ⟨stage_tma_components a b frame,stage_schedules_admitted a b,tensor_component a b,
    stage_memory_witness a b frame,stage_observer_witness a b frame⟩

def omittedObservation (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) : Unified.Observation :=
  {observation a b frame with domain := []}
def staleObservation (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) : Unified.Observation :=
  {observation a b frame with source := fun _ => none, output := representedInitial a b frame}
theorem omitted_output_rejected (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b)
      (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster (omittedObservation a b frame) := by
  intro ho
  have hh := ho.coverage _ _ _ rfl (actual_output_byte a b 0 0 0)
  cases hh
theorem stale_output_rejected (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) :
    ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b)
      (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster (staleObservation a b frame) := by
  intro ho
  have hw := actual_output_byte a b 0 0 0
  have hd : ((⟨.global,wordAddress 0 0⟩ : Location).add 0) ∈ outputDomain := by
    apply mem_output_domain.mpr
    have hb := word_address_bounds 0 0
    exact ⟨rfl,by dsimp [Location.add]; omega,by dsimp [Location.add]; omega⟩
  have hh := ho.noStale _ hd (stage_no_mixed_size_race a b readWitness) _ _ hw
  exact hh ⟨rfl,_,rfl,Option.isSome_iff_exists.mpr ⟨_,hw⟩⟩

end
end Ptx.Kernels.HopperStage
