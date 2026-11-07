import Ptx.Kernels.HopperStageRegionRules
import Ptx.Kernels.HopperDoubleBufferSourceFootprints
import Ptx.Hopper.UnifiedMixedSize

/-! Exhaustive actual footprint regions across ordinary/TMA/native accesses.
Shared accesses are single bytes; aligned output words are disjoint from
packed input bytes and tensor maps. No RF/co or race premise is used here. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_tensor_write_footprint {a b tiles id offset base size} (hb : tiles ≤ 2^28)
    (hf : (Access.kind Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view (.tma (.write id offset))).bind
      Ptx.Event.Kind.footprint = some (base,size)) : HopperStage.SharedByte base size := by
  cases hk : Access.kind Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view (.tma (.write id offset)) with
  | none => simp only [hk,Option.bind_none] at hf; cases hf
  | some kind =>
    obtain ⟨loc,value,hl,_,rfl⟩ := Access.tensor_write_shape hk
    have he : loc = base ∧ 1 = size := by
      simpa only [hk,Option.bind_some,Ptx.Event.Kind.footprint,List.length_singleton,Option.some.injEq,Prod.mk.injEq] using hf
    obtain ⟨tile,ht,hregion⟩ := data_tensor_write_region hb hl
    have hs : loc.space = .shared .zero := by
      rcases hregion with ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩ <;> rfl
    exact ⟨he.1 ▸ hs,he.2.symm⟩

theorem data_all_footprint_regions {a b tiles node base size} (hb : tiles ≤ 2^28)
    (hf : (Unified.kind Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) node).bind
      Ptx.Event.Kind.footprint = some (base,size)) : HopperStage.Region base size := by
  cases node with
  | wgmmaRead issue operand =>
    cases he : (dataCompleteCandidate a b tiles).representativeAt issue with
    | none => simp only [Unified.kind,he,Option.map_none,Option.bind_none] at hf; cases hf
    | some pair =>
      have hc := data_event_cta_zero (Unified.representative_at he).1
      have hh : Wgmma.operandLocation issue.thread.cta pair.2 operand = base ∧ 1 = size := by
        simpa only [Unified.kind,he,Option.map_some,Option.bind_some,Wgmma.operandKind,
          Ptx.Event.Kind.footprint,List.length_singleton,Option.some.injEq,Prod.mk.injEq] using hf
      apply Or.inl
      refine ⟨?_,hh.2.symm⟩
      rw [← hh.1]
      cases operand <;> simpa only [Wgmma.operandLocation,hc]
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.kind,Access.kind,data_no_nonbulk] at hf
    | tma node =>
      cases node with
      | source event => exact .inr (.inl (data_source_word_region hf))
      | notify id => cases hf
      | write id offset => exact .inl (data_tensor_write_footprint hb hf)
      | descriptor id =>
        cases hc : Tma.copyAt (dataCompleteCandidate a b tiles).view id with
        | none => simp only [Unified.kind,Access.kind,hc,Option.map_none,Option.bind_none] at hf; cases hf
        | some op =>
          obtain ⟨tile,ht,hcopy⟩ := data_all_source_copies a b tiles hb id op hc
          rcases hcopy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · have he : (⟨.global,4096⟩ : Location) = base ∧ 128 = size := by
              simpa only [Unified.kind,Access.kind,hc,Option.map_some,Option.bind_some,
                Ptx.Event.Kind.footprint,TensorMap.encode_length,Access.globalDescriptor,dataCopyA,Option.some.injEq,Prod.mk.injEq] using hf
            rcases he with ⟨rfl,rfl⟩
            exact .inr (.inr (.inr ⟨rfl,rfl,by decide⟩))
          · have he : (⟨.global,4224⟩ : Location) = base ∧ 128 = size := by
              simpa only [Unified.kind,Access.kind,hc,Option.map_some,Option.bind_some,
                Ptx.Event.Kind.footprint,TensorMap.encode_length,Access.globalDescriptor,dataCopyB,Option.some.injEq,Prod.mk.injEq] using hf
            rcases he with ⟨rfl,rfl⟩
            exact .inr (.inr (.inr ⟨rfl,rfl,by decide⟩))
      | read id offset =>
        cases hk : Access.kind Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view (.tma (.read id offset)) with
        | none => simp only [Unified.kind,hk,Option.bind_none] at hf; cases hf
        | some kind =>
          obtain ⟨loc,value,hl,_,rfl⟩ := Access.tensor_read_shape hk
          have he : loc = base ∧ 1 = size := by
            simpa only [Unified.kind,hk,Option.bind_some,Ptx.Event.Kind.footprint,
              List.length_singleton,Option.some.injEq,Prod.mk.injEq] using hf
          rcases he with ⟨rfl,rfl⟩
          cases hc : Tma.copyAt (dataCompleteCandidate a b tiles).view id with
          | none => simp only [Tma.readLocation,hc,Option.bind_none] at hl; cases hl
          | some op =>
            have hs : Tma.sourceByte op.descriptor op.coordinates offset = some loc := by
              simpa only [Tma.readLocation,hc,Option.bind_some] using hl
            obtain ⟨_,_,hg,ha⟩ := Tma.source_byte_some hs
            apply Or.inr; apply Or.inr; apply Or.inl
            refine ⟨hg,rfl,?_⟩
            obtain ⟨tile,ht,hcopy⟩ := data_all_source_copies a b tiles hb id op hc
            rcases hcopy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
            · dsimp only [dataCopyA,aView] at ha
              omega
            · dsimp only [dataCopyB,bView,dataBBase] at ha
              omega

theorem data_write_footprint_regions {a b tiles node loc value} (hb : tiles ≤ 2^28)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) node loc = some value) :
    ∃ base size, (Unified.kind Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) node).bind
      Ptx.Event.Kind.footprint = some (base,size) ∧ (HopperStage.SharedByte base size ∨ HopperStage.OutputWord base size) := by
  obtain ⟨base,size,hf⟩ := Unified.access_footprint_exists (.inr (by rw [hw]; rfl))
  refine ⟨base,size,hf,?_⟩
  cases node with
  | wgmmaRead issue operand => rw [Unified.native_write_none] at hw; cases hw
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.kind,Access.kind,data_no_nonbulk] at hf
    | tma node =>
      cases node with
      | source event => exact .inr (data_source_word_region hf)
      | write id offset => exact .inl (data_tensor_write_footprint hb hf)
      | descriptor id => rw [Unified.base_write_preserved,Access.descriptor_no_write] at hw; cases hw
      | read id offset => rw [Unified.base_write_preserved,Access.tensor_read_no_write] at hw; cases hw
      | notify id => cases hw

theorem data_conflicting_footprints_equal {a b tiles writer other loc value} (hb : tiles ≤ 2^28)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) writer loc = some value)
    (ha : Unified.Accesses Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) other loc) :
    Unified.SameFootprint Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) writer other := by
  obtain ⟨wb,ws,hfw,hwreg⟩ := data_write_footprint_regions hb hw
  obtain ⟨rb,rs,hfr⟩ := Unified.access_footprint_exists ha
  have hrreg := data_all_footprint_regions hb hfr
  have hwb := Unified.access_footprint_bounds (.inr (by rw [hw]; rfl)) hfw
  have hrb := Unified.access_footprint_bounds ha hfr
  suffices he : wb = rb ∧ ws = rs by
    refine ⟨(wb,ws),hfw,?_⟩
    rw [he.1,he.2]
    exact hfr
  exact HopperStage.overlapping_regions_equal hwreg hrreg hwb hrb

end
end Ptx.Kernels.HopperDoubleBuffer
