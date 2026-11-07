import Ptx.Kernels.HopperDoubleBufferCandidateInputs
import Ptx.Kernels.HopperStageRegionRules
import Ptx.Hopper.UnifiedMixedSize

/-! Whole-inventory mixed-size compatibility for arbitrary completed source
candidates with the existing TMA descriptor admission. No chosen data witness,
payload values, RF/co, resource history or race-freedom premise is used.
This excludes mixed-size races, not all same-size data races. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem candidate_event_cta_zero {tiles initial candidate id event}
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (he : candidate.eventAt id = some event) : id.thread.cta = .zero := by
  obtain ⟨trace,ht,hid,_⟩ := Unified.eventAt_trace he
  obtain ⟨lane,hlane⟩ := HopperStage.ctx_covered (hw.2.2.1 trace ht).1
  rw [← hid,← hlane]
  rfl

theorem candidate_tma_write_shared_space {tiles initial candidate id offset loc}
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hl : Tma.writeLocation Tma.localShared candidate.view id offset = some loc) : loc.space = .shared .zero := by
  cases he : Tma.copyAt candidate.view id with
  | none => simp only [Tma.writeLocation,he,Option.bind_none] at hl; cases hl
  | some copy =>
    have hcta := candidate_event_cta_zero hw (Unified.view_tma_iff.mp (Tma.copyAt_iff.mp he))
    simp only [Tma.writeLocation,he,Option.bind_some] at hl
    split at hl
    · have hs := (congrArg Location.space (Option.some.inj hl)).symm
      simpa only [Tma.localShared,Location.add,hcta] using hs
    · cases hl

theorem candidate_tma_write_footprint {tiles initial candidate id offset base size}
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hf : (Access.kind Tma.localShared Access.globalDescriptor candidate.view (.tma (.write id offset))).bind
      Ptx.Event.Kind.footprint = some (base,size)) : HopperStage.SharedByte base size := by
  cases hk : Access.kind Tma.localShared Access.globalDescriptor candidate.view (.tma (.write id offset)) with
  | none => simp only [hk,Option.bind_none] at hf; cases hf
  | some kind =>
    obtain ⟨loc,value,hl,_,rfl⟩ := Access.tensor_write_shape hk
    have he : loc = base ∧ 1 = size := by
      simpa only [hk,Option.bind_some,Ptx.Event.Kind.footprint,List.length_singleton,Option.some.injEq,Prod.mk.injEq] using hf
    exact ⟨he.1 ▸ candidate_tma_write_shared_space hw hl,he.2.symm⟩

theorem candidate_descriptor_footprint {tiles initial candidate id base size} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hf : (Access.kind Tma.localShared Access.globalDescriptor candidate.view (.tma (.descriptor id))).bind
      Ptx.Event.Kind.footprint = some (base,size)) :
    base.space = .global ∧ size = 128 ∧ base.address+128 ≤ 4352 := by
  cases he : Tma.copyAt candidate.view id with
  | none => simp only [Access.kind,he,Option.map_none,Option.bind_none] at hf; cases hf
  | some copy =>
    obtain ⟨tile,_,ha | hb'⟩ := candidate_copy_geometry hb hw hc he
    · have hx : (⟨.global,4096⟩ : Location) = base ∧ 128 = size := by
        simpa only [Access.kind,he,Option.map_some,Option.bind_some,Ptx.Event.Kind.footprint,
          TensorMap.encode_length,Access.globalDescriptor,ha.1,Option.some.injEq,Prod.mk.injEq] using hf
      rcases hx with ⟨rfl,rfl⟩
      exact ⟨rfl,rfl,by decide⟩
    · have hx : (⟨.global,4224⟩ : Location) = base ∧ 128 = size := by
        simpa only [Access.kind,he,Option.map_some,Option.bind_some,Ptx.Event.Kind.footprint,
          TensorMap.encode_length,Access.globalDescriptor,hb'.1,Option.some.injEq,Prod.mk.injEq] using hf
      rcases hx with ⟨rfl,rfl⟩
      exact ⟨rfl,rfl,by decide⟩

theorem candidate_all_footprint_regions {tiles initial candidate node base size} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hf : (Unified.kind Tma.localShared Access.globalDescriptor candidate node).bind
      Ptx.Event.Kind.footprint = some (base,size)) : HopperStage.Region base size := by
  cases node with
  | wgmmaRead issue operand =>
    cases he : candidate.representativeAt issue with
    | none => simp only [Unified.kind,he,Option.map_none,Option.bind_none] at hf; cases hf
    | some pair =>
      have hcta := candidate_event_cta_zero hw (Unified.representative_at he).1
      have hh : Wgmma.operandLocation issue.thread.cta pair.2 operand = base ∧ 1 = size := by
        simpa only [Unified.kind,he,Option.map_some,Option.bind_some,Wgmma.operandKind,
          Ptx.Event.Kind.footprint,List.length_singleton,Option.some.injEq,Prod.mk.injEq] using hf
      apply Or.inl
      refine ⟨?_,hh.2.symm⟩
      rw [← hh.1]
      cases operand <;> simp only [Wgmma.operandLocation,hcta]
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.kind,Access.kind,candidate_no_nonbulk hb hw hc] at hf
    | tma node =>
      cases node with
      | source event => exact .inr (.inl (candidate_source_word_region hb hw hc hf))
      | notify id => cases hf
      | write id offset => exact .inl (candidate_tma_write_footprint hw hf)
      | descriptor id => exact .inr (.inr (.inr (candidate_descriptor_footprint hb hw hc hf)))
      | read id offset =>
        cases hk : Access.kind Tma.localShared Access.globalDescriptor candidate.view (.tma (.read id offset)) with
        | none => simp only [Unified.kind,hk,Option.bind_none] at hf; cases hf
        | some kind =>
          obtain ⟨loc,value,hl,_,rfl⟩ := Access.tensor_read_shape hk
          have he : loc = base ∧ 1 = size := by
            simpa only [Unified.kind,hk,Option.bind_some,Ptx.Event.Kind.footprint,
              List.length_singleton,Option.some.injEq,Prod.mk.injEq] using hf
          rcases he with ⟨rfl,rfl⟩
          have hg := candidate_tma_read_input_bounds hb hw hc hd hl
          exact .inr (.inr (.inl ⟨hg.1,rfl,hg.2⟩))

theorem candidate_write_footprint_regions {tiles initial candidate node loc value} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hwrite : Unified.writeByte Tma.localShared Access.globalDescriptor candidate node loc = some value) :
    ∃ base size, (Unified.kind Tma.localShared Access.globalDescriptor candidate node).bind
      Ptx.Event.Kind.footprint = some (base,size) ∧ (HopperStage.SharedByte base size ∨ HopperStage.OutputWord base size) := by
  obtain ⟨base,size,hf⟩ := Unified.access_footprint_exists (.inr (by rw [hwrite]; rfl))
  refine ⟨base,size,hf,?_⟩
  cases node with
  | wgmmaRead issue operand => rw [Unified.native_write_none] at hwrite; cases hwrite
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.kind,Access.kind,candidate_no_nonbulk hb hw hc] at hf
    | tma node =>
      cases node with
      | source event => exact .inr (candidate_source_word_region hb hw hc hf)
      | write id offset => exact .inl (candidate_tma_write_footprint hw hf)
      | descriptor id => rw [Unified.base_write_preserved,Access.descriptor_no_write] at hwrite; cases hwrite
      | read id offset => rw [Unified.base_write_preserved,Access.tensor_read_no_write] at hwrite; cases hwrite
      | notify id => cases hwrite

theorem candidate_conflicting_footprints_equal {tiles initial candidate writer other loc value} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hwrite : Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer loc = some value)
    (ha : Unified.Accesses Tma.localShared Access.globalDescriptor candidate other loc) :
    Unified.SameFootprint Tma.localShared Access.globalDescriptor candidate writer other := by
  obtain ⟨wb,ws,hfw,hwreg⟩ := candidate_write_footprint_regions hb hw hc hwrite
  obtain ⟨rb,rs,hfr⟩ := Unified.access_footprint_exists ha
  have hrreg := candidate_all_footprint_regions hb hw hc hd hfr
  have hwb := Unified.access_footprint_bounds (.inr (by rw [hwrite]; rfl)) hfw
  have hrb := Unified.access_footprint_bounds ha hfr
  obtain ⟨rfl,rfl⟩ := HopperStage.overlapping_regions_equal hwreg hrreg hwb hrb
  exact ⟨_,hfw,hfr⟩

theorem candidate_no_mixed_size_race {tiles initial candidate histories cluster rf} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) :
    ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor candidate histories cluster rf :=
  Unified.compatible_conflicts_no_mixed_size_race (fun _ _ _ _ => candidate_conflicting_footprints_equal hb hw hc hd)

end
end Ptx.Kernels.HopperDoubleBuffer
