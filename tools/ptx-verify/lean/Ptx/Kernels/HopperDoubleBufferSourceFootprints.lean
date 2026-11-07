import Ptx.Kernels.HopperDoubleBufferMemoryInputs
import Ptx.Kernels.HopperStageAccessRegions

/-! Exhaustive ordinary-source footprints for arbitrary real-data repeated
execution. The output layout and region definitions are shared with the
one-stage baseline; actual source identities/bytes come from this source. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem memory_shape_footprint_write {event : Wgmma.Event} {base size}
    (hs : sourceMemoryShape event = true)
    (hf : HopperStage.eventFootprint (Unified.eventView event) = some (base,size)) :
    ∃ bytes, globalWrite event = some (base.address,bytes) ∧ base.space = .global ∧ size = bytes.length := by
  cases event with
  | base event =>
    cases event with
    | ampere event =>
      cases event with
      | ordinary kind =>
        cases kind <;> try cases hs <;> try cases hf
        case write loc bytes =>
          have he : loc = base ∧ bytes.length = size := Prod.mk.inj (Option.some.inj hf)
          rcases he with ⟨rfl,rfl⟩
          have hg : loc.space = .global := by simpa only [sourceMemoryShape,Unified.eventView,memoryShape,beq_iff_eq] using hs
          cases loc with
          | mk space address =>
            change space = .global at hg
            subst space
            exact ⟨bytes,rfl,rfl,rfl⟩
      | issue _ _ | commit _ | wait _ _ | mmaEntry _ | mmaReturn _ => cases hf
    | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ => cases hf
  | fence _ | mma _ _ | commit _ _ | wait _ _ _ _ _ _ => cases hf

theorem data_source_footprint_owner {a b tiles id base size}
    (hf : (Access.kind Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view (.tma (.source id))).bind
      Ptx.Event.Kind.footprint = some (base,size)) :
    ∃ lane slot, id.thread = (ctx tiles lane).id ∧ base = ⟨.global,outputWordAddress (lane,slot)⟩ ∧ size = 4 := by
  cases he : (dataCompleteCandidate a b tiles).view.eventAt id with
  | none => simp only [Access.kind,he,Option.bind_none] at hf; cases hf
  | some event =>
    have hfp : HopperStage.eventFootprint event = some (base,size) := by
      simp only [Access.kind,he,Option.bind_some] at hf
      cases event with
      | ampere event => cases event <;> exact hf
      | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ => exact hf
    rw [Unified.view_eventAt] at he
    obtain ⟨rich,hr,hview⟩ := Option.map_eq_some_iff.mp he
    have hrfoot : HopperStage.eventFootprint (Unified.eventView rich) = some (base,size) := by rw [hview]; exact hfp
    obtain ⟨bytes,hwrite,hspace,hsize⟩ := memory_shape_footprint_write (data_candidate_memory_shape hr) hrfoot
    obtain ⟨trace,ht,hid,hget⟩ := Unified.eventAt_trace hr
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
    have hm : (base.address,bytes) ∈ (dataCompleteEvents a b tiles lane).filterMap globalWrite :=
      List.mem_filterMap.mpr ⟨rich,List.mem_of_getElem? hget,hwrite⟩
    rw [data_complete_write_specification] at hm
    obtain ⟨slot,hpair⟩ := List.mem_ofFn.mp hm
    have ha := congrArg Prod.fst hpair
    have hb := congrArg Prod.snd hpair
    simp only at hb
    have hn : size = 4 := by rw [hsize,← hb,Symbolic.encode_length]; rfl
    simp only at ha
    refine ⟨lane,slot,hid.symm,?_,hn⟩
    cases base with
    | mk space address =>
      exact congrArg₂ Location.mk hspace ha.symm

theorem data_source_word_region {a b tiles id base size}
    (hf : (Access.kind Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view (.tma (.source id))).bind
      Ptx.Event.Kind.footprint = some (base,size)) : HopperStage.OutputWord base size := by
  obtain ⟨lane,slot,_,rfl,rfl⟩ := data_source_footprint_owner hf
  have hrow := (Wgmma.cCoord (lane,slot)).1.isLt
  have hcol := (Wgmma.cCoord (lane,slot)).2.isLt
  refine ⟨rfl,rfl,?_,?_,?_⟩ <;> dsimp [outputWordAddress] <;> omega

theorem data_event_cta_zero {a b tiles id event}
    (he : (dataCompleteCandidate a b tiles).eventAt id = some event) : id.thread.cta = .zero := by
  obtain ⟨trace,ht,hid,_⟩ := Unified.eventAt_trace he
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  rw [← hid]
  rfl

end
end Ptx.Kernels.HopperDoubleBuffer
