import Ptx.Kernels.HopperDoubleBufferMemoryWitness

/-! Source-indexed output stores. The actual event serial, not just the
unindexed output address inventory, identifies the unique global writer.
Shared bytes may still have many TMA writers across reused rounds. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataStoreId (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) (slot : Wgmma.Slot) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,(dataPreOutputEvents a b tiles lane).length+slot.val⟩

theorem output_write_event_at (lane : Wgmma.Lane) (values : Fin 4 → ℝ) (slot : Wgmma.Slot) :
    (outputWriteEvents lane values)[slot.val]? = some (outputWriteEvent lane values slot) := by
  fin_cases slot <;> rfl

theorem data_complete_store_event (a b tiles lane slot) :
    (dataCompleteCandidate a b tiles).eventAt (dataStoreId a b tiles lane slot) =
      some (outputWriteEvent lane (fun slot => result a b tiles (Wgmma.cCoord (lane,slot))) slot) := by
  change (dataCompleteCandidate a b tiles).eventAt ⟨(dataCompleteTrace a b tiles lane).id,(dataPreOutputEvents a b tiles lane).length+slot.val⟩ = _
  rw [Unified.eventAt_of_member (data_source_ids_unique a b tiles) (List.mem_ofFn.mpr ⟨lane,rfl⟩)]
  change (dataPreOutputEvents a b tiles lane++(outputWriteEvents lane _++_))[(dataPreOutputEvents a b tiles lane).length+slot.val]? = _
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,List.getElem?_append_left]
  · exact output_write_event_at lane _ slot
  · simpa only [outputWriteEvents,List.length_cons,List.length_nil] using slot.isLt

theorem data_complete_global_write_case {a b tiles lane index event address bytes}
    (he : (dataCompleteEvents a b tiles lane)[index]? = some event)
    (hw : globalWrite event = some (address,bytes)) :
    ∃ slot : Wgmma.Slot, index = (dataStoreId a b tiles lane slot).serial ∧
      address = outputWordAddress (lane,slot) ∧
      bytes = Symbolic.encode .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) := by
  by_cases hp : index < (dataPreOutputEvents a b tiles lane).length
  · rw [dataCompleteEvents,List.getElem?_append_left hp] at he
    have hm := List.mem_filterMap.mpr ⟨event,List.mem_of_getElem? he,hw⟩
    rw [data_pre_output_no_global_write] at hm
    cases hm
  · rw [dataCompleteEvents,List.getElem?_append_right (by omega),outputEvents] at he
    by_cases hi : index-(dataPreOutputEvents a b tiles lane).length < 4
    · let slot : Wgmma.Slot := ⟨index-(dataPreOutputEvents a b tiles lane).length,hi⟩
      rw [List.getElem?_append_left (by simpa only [outputWriteEvents,List.length_cons,List.length_nil] using hi)] at he
      have hs := output_write_event_at lane (fun slot => result a b tiles (Wgmma.cCoord (lane,slot))) slot
      rw [hs] at he
      cases he
      have hh := Prod.mk.inj (Option.some.inj hw)
      refine ⟨slot,by dsimp [dataStoreId,slot]; omega,?_,?_⟩
      · exact hh.1.symm.trans (output_write_address lane slot)
      · rw [← hh.2]
        exact congrArg (Symbolic.encode .f32) (result_matches_specification a b tiles (Wgmma.cCoord (lane,slot)))
    · rw [List.getElem?_append_right (by simpa only [outputWriteEvents,List.length_cons,List.length_nil] using (show 4 ≤ index-(dataPreOutputEvents a b tiles lane).length by omega))] at he
      have hm := List.mem_filterMap.mpr ⟨event,List.mem_of_getElem? he,hw⟩
      rw [return_no_global_write] at hm
      cases hm

theorem data_source_indexed_footprint {a b tiles id base size}
    (hf : (Access.kind Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view (.tma (.source id))).bind
      Ptx.Event.Kind.footprint = some (base,size)) :
    ∃ lane slot, id = dataStoreId a b tiles lane slot ∧ base = ⟨.global,outputWordAddress (lane,slot)⟩ ∧ size = 4 := by
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
    obtain ⟨slot,hserial,haddress,hbytes⟩ := data_complete_global_write_case hget hwrite
    refine ⟨lane,slot,?_,?_,?_⟩
    · cases id with | mk thread serial => exact congrArg₂ Ptx.Event.EventId.mk hid.symm hserial
    · cases base with | mk space address => exact congrArg₂ Location.mk hspace haddress
    · rw [hsize,hbytes,Symbolic.encode_length]; rfl

theorem data_global_writer_metadata {a b tiles writer loc value} (hb : tiles ≤ 2^28) (hg : loc.space = .global)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) writer loc = some value) :
    ∃ lane slot, writer = .base (.tma (.source (dataStoreId a b tiles lane slot))) ∧
      outputWordAddress (lane,slot) ≤ loc.address ∧ loc.address < outputWordAddress (lane,slot)+4 := by
  obtain ⟨id,rfl⟩ := data_global_writer_source hb hg hw
  obtain ⟨base,size,hf⟩ := Unified.access_footprint_exists (.inr (by rw [hw]; rfl))
  obtain ⟨lane,slot,rfl,rfl,rfl⟩ := data_source_indexed_footprint hf
  have hr := Unified.access_footprint_bounds (.inr (by rw [hw]; rfl)) hf
  exact ⟨lane,slot,rfl,hr.2.1,hr.2.2⟩

theorem data_global_unique_writers {a b tiles loc left right lv rv} (hb : tiles ≤ 2^28) (hg : loc.space = .global)
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) left loc = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) right loc = some rv) : left = right := by
  obtain ⟨ll,ls,rfl,hleft⟩ := data_global_writer_metadata hb hg hl
  obtain ⟨rl,rs,rfl,hright⟩ := data_global_writer_metadata hb hg hr
  have he : outputWordAddress (ll,ls) = outputWordAddress (rl,rs) := by dsimp [outputWordAddress] at hleft hright ⊢; omega
  have ho := (output_byte_unique (left := (ll,ls)) (right := (rl,rs)) (i := 0) (j := 0)
    (by simpa only [outputByteAddress,Fin.val_zero,Nat.add_zero] using he)).1
  have hlanes := congrArg Prod.fst ho
  have hslots := congrArg Prod.snd ho
  cases hlanes
  cases hslots
  rfl

end
end Ptx.Kernels.HopperDoubleBuffer
