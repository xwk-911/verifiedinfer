import Ptx.Kernels.HopperDoubleBufferReplyInventory

/-! Actual ordinary/TMA writer classification and global-input immutability
for any well-formed completed candidate, not only the constructed RF witness.
This chooses no RF/co, admits no history and assumes no matrix output value.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem candidate_no_nonbulk {tiles initial candidate} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate) (id : Ptx.Event.EventId) :
    Access.copyAt candidate.view id = none := by
  cases he : Access.copyAt candidate.view id with
  | none => rfl
  | some op =>
    obtain ⟨ordinal,hissue⟩ := Access.nonbulk_has_actual_issue he
    have hh := candidate_view_memory_shape hb hw hc hissue
    cases hh

theorem candidate_ordinary_read_none {tiles initial candidate} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (id : Ptx.Event.EventId) (loc : Location) :
    Access.readByte Tma.localShared Access.globalDescriptor candidate.view (.tma (.source id)) loc = none := by
  cases he : candidate.view.eventAt id with
  | none => simp only [Access.readByte,Access.kind,he,Option.bind_none]
  | some event =>
    have hs := candidate_view_memory_shape hb hw hc he
    simp only [Access.readByte,Access.kind,he,Option.bind_some]
    cases event with
    | ampere event =>
      cases event with
      | ordinary kind => cases kind <;> first | rfl | cases hs
      | issue _ _ | commit _ | wait _ _ | mmaEntry _ | mmaReturn _ => rfl
    | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ => rfl

theorem candidate_ordinary_shared_write_none {tiles initial candidate} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (id : Ptx.Event.EventId) (loc : Location) (cta : Dim3) (hl : loc.space = .shared cta) :
    Access.writeByte Tma.localShared Access.globalDescriptor candidate.view (.tma (.source id)) loc = none := by
  cases he : candidate.view.eventAt id with
  | none => simp only [Access.writeByte,Access.kind,he,Option.bind_none]
  | some event =>
    have hs := candidate_view_memory_shape hb hw hc he
    simp only [Access.writeByte,Access.kind,he,Option.bind_some]
    cases event with
    | ampere event =>
      cases event with
      | ordinary kind =>
        cases kind <;> try cases hs
        case write base bytes =>
          have hg : base.space = .global := by simpa only [memoryShape,beq_iff_eq] using hs
          simp [Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte,hg,hl]
        all_goals rfl
      | issue _ _ | commit _ | wait _ _ | mmaEntry _ | mmaReturn _ => rfl
    | tmaIssue _ | proxyFenceAsyncShared _ | barrier _ | wgmma _ => rfl

theorem candidate_source_footprint_owner {tiles initial candidate id base size} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hf : (Access.kind Tma.localShared Access.globalDescriptor candidate.view (.tma (.source id))).bind
      Ptx.Event.Kind.footprint = some (base,size)) :
    ∃ lane slot, id.thread = (ctx tiles lane).id ∧ base = ⟨.global,outputWordAddress (lane,slot)⟩ ∧ size = 4 := by
  cases he : candidate.view.eventAt id with
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
    obtain ⟨bytes,hwrite,hspace,hsize⟩ := memory_shape_footprint_write (candidate_event_memory_shape hb hw hc hr) hrfoot
    obtain ⟨trace,ht,hid,hget⟩ := Unified.eventAt_trace hr
    obtain ⟨lane,hthread,values,houtputs⟩ := candidate_trace_write_inventory hb hw hc ht
    have hm := List.mem_filterMap.mpr ⟨rich,List.mem_of_getElem? hget,hwrite⟩
    rw [houtputs] at hm
    obtain ⟨slot,hpair⟩ := List.mem_ofFn.mp hm
    have ha := congrArg Prod.fst hpair
    have hbytes := congrArg Prod.snd hpair
    simp only at ha hbytes
    refine ⟨lane,slot,hid.symm.trans hthread,?_,?_⟩
    · cases base with | mk space address => exact congrArg₂ Location.mk hspace ha.symm
    · rw [hsize,← hbytes,Symbolic.encode_length]; rfl

theorem candidate_source_word_region {tiles initial candidate id base size} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hf : (Access.kind Tma.localShared Access.globalDescriptor candidate.view (.tma (.source id))).bind
      Ptx.Event.Kind.footprint = some (base,size)) : HopperStage.OutputWord base size := by
  obtain ⟨lane,slot,_,rfl,rfl⟩ := candidate_source_footprint_owner hb hw hc hf
  have hr := (Wgmma.cCoord (lane,slot)).1.isLt
  have hcol := (Wgmma.cCoord (lane,slot)).2.isLt
  refine ⟨rfl,rfl,?_,?_,?_⟩ <;> dsimp [outputWordAddress] <;> omega

theorem candidate_shared_writer_is_tensor {tiles initial candidate writer loc value cta} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate) (hl : loc.space = .shared cta)
    (hwrite : Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer loc = some value) :
    ∃ id offset, writer = .base (.tma (.write id offset)) ∧ Tma.writeLocation Tma.localShared candidate.view id offset = some loc := by
  cases writer with
  | wgmmaRead issue operand => rw [Unified.native_write_none] at hwrite; cases hwrite
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.writeByte,Unified.kind,Access.kind,candidate_no_nonbulk hb hw hc] at hwrite
    | tma node =>
      cases node with
      | source id => rw [Unified.base_write_preserved,candidate_ordinary_shared_write_none hb hw hc id loc cta hl] at hwrite; cases hwrite
      | descriptor id => rw [Unified.base_write_preserved,Access.descriptor_no_write] at hwrite; cases hwrite
      | read id offset => rw [Unified.base_write_preserved,Access.tensor_read_no_write] at hwrite; cases hwrite
      | notify id => cases hwrite
      | write id offset => exact ⟨id,offset,rfl,Access.tensor_write_access (.inr (by rw [← Unified.base_write_preserved,hwrite]; rfl))⟩

theorem candidate_global_writer_is_source {tiles initial candidate writer loc value} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate) (hg : loc.space = .global)
    (hwrite : Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer loc = some value) :
    ∃ id, writer = .base (.tma (.source id)) := by
  cases writer with
  | wgmmaRead issue operand => rw [Unified.native_write_none] at hwrite; cases hwrite
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.writeByte,Unified.kind,Access.kind,candidate_no_nonbulk hb hw hc] at hwrite
    | tma node =>
      cases node with
      | source id => exact ⟨id,rfl⟩
      | descriptor id => rw [Unified.base_write_preserved,Access.descriptor_no_write] at hwrite; cases hwrite
      | read id offset => rw [Unified.base_write_preserved,Access.tensor_read_no_write] at hwrite; cases hwrite
      | notify id => cases hwrite
      | write id offset =>
        have hl := Access.tensor_write_access (.inr (by rw [← Unified.base_write_preserved,hwrite]; rfl))
        cases he : Tma.copyAt candidate.view id with
        | none => simp only [Tma.writeLocation,he,Option.bind_none] at hl; cases hl
        | some op =>
          simp only [Tma.writeLocation,he,Option.bind_some] at hl
          split at hl
          · have hs := congrArg Location.space (Option.some.inj hl)
            simp only [Tma.localShared,Location.add,hg] at hs
            cases hs
          · cases hl

theorem candidate_global_write_bounds {tiles initial candidate writer loc value} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate) (hg : loc.space = .global)
    (hwrite : Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer loc = some value) :
    8192 ≤ loc.address ∧ loc.address < 10240 := by
  obtain ⟨id,rfl⟩ := candidate_global_writer_is_source hb hw hc hg hwrite
  obtain ⟨base,size,hf⟩ := Unified.access_footprint_exists (.inr (by rw [hwrite]; rfl))
  have hregion := candidate_source_word_region hb hw hc hf
  have hbounds := Unified.access_footprint_bounds (.inr (by rw [hwrite]; rfl)) hf
  have hsize := hregion.2.1
  exact ⟨by have := hregion.2.2.1; omega,by have := hregion.2.2.2.1; omega⟩

theorem candidate_global_outside_output_immutable {tiles initial candidate loc} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate) (hg : loc.space = .global)
    (hout : ¬(8192 ≤ loc.address ∧ loc.address < 10240)) (writer : Unified.Node) :
    Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer loc = none := by
  cases he : Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer loc with
  | none => rfl
  | some value => exact (hout (candidate_global_write_bounds hb hw hc hg he)).elim

end
end Ptx.Kernels.HopperDoubleBuffer
