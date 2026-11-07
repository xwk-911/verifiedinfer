import Ptx.Kernels.HopperDoubleBufferRetryArithmetic
import Ptx.Kernels.HopperDoubleBufferStoreInventory

/-! Actual indexed output stores for arbitrary-retry source families. Global
writer uniqueness is derived from source serials and output ownership, without
assuming uniqueness of the repeatedly written shared-memory buffers. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def ReplySourceFamily.storeId {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles+slot.val⟩

theorem reply_complete_store_event (tiles lane reply retries) (slot : Wgmma.Slot) :
    (replyPositiveEvents tiles lane reply retries)[replyTileStart tiles lane reply retries tiles+slot.val]? =
      some (outputWriteEvent lane (replyCheckpoint tiles lane reply retries).2 slot) := by
  simp only [replyPositiveEvents,← List.append_assoc]
  change ((replyInitialEvents lane reply++replyLoopEvents tiles lane reply retries tiles)++
    (outputWriteEvents lane _++_))[_]? = _
  rw [List.getElem?_append_right (by simp only [List.length_append]; unfold replyTileStart; omega)]
  rw [show replyTileStart tiles lane reply retries tiles+slot.val-
      (replyInitialEvents lane reply++replyLoopEvents tiles lane reply retries tiles).length = slot.val by
    simp only [List.length_append,replyTileStart]; omega]
  rw [List.getElem?_append_left]
  · exact output_write_event_at lane _ slot
  · simpa only [outputWriteEvents,List.length_cons,List.length_nil] using slot.isLt

theorem family_store_event {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (lane : Wgmma.Lane) (slot : Wgmma.Slot) :
    candidate.eventAt (family.storeId lane slot) =
      some (outputWriteEvent lane (replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).2 slot) :=
  family_event_at family hw lane _ _ (reply_complete_store_event tiles lane (family.replies lane) (family.schedules lane) slot)

theorem reply_complete_global_write_case {tiles lane reply retries index event address bytes}
    (he : (replyPositiveEvents tiles lane reply retries)[index]? = some event)
    (hw : globalWrite event = some (address,bytes)) :
    ∃ slot : Wgmma.Slot, index = replyTileStart tiles lane reply retries tiles+slot.val ∧
      address = outputWordAddress (lane,slot) ∧
      bytes = Symbolic.encode .f32 ((replyCheckpoint tiles lane reply retries).2 slot) := by
  simp only [replyPositiveEvents,← List.append_assoc] at he
  change ((replyInitialEvents lane reply++replyLoopEvents tiles lane reply retries tiles)++_)[index]? = some event at he
  by_cases hp : index < replyTileStart tiles lane reply retries tiles
  · rw [List.getElem?_append_left (by simpa only [List.length_append,replyTileStart] using hp)] at he
    have hm := List.mem_filterMap.mpr ⟨event,List.mem_of_getElem? he,hw⟩
    simp only [List.filterMap_append,replyInitialEvents,replyLoopEvents,initialization_no_global_write,
      reply_initial_no_global_write,loop_no_global_write,List.nil_append] at hm
    cases hm
  · rw [List.getElem?_append_right (by simpa only [List.length_append,replyTileStart] using Nat.le_of_not_gt hp)] at he
    have hlen : (replyInitialEvents lane reply++replyLoopEvents tiles lane reply retries tiles).length =
        replyTileStart tiles lane reply retries tiles := by simp only [List.length_append,replyTileStart]
    rw [hlen] at he
    change (outputWriteEvents lane _++_)[index-replyTileStart tiles lane reply retries tiles]? = some event at he
    by_cases hi : index-replyTileStart tiles lane reply retries tiles < 4
    · let slot : Wgmma.Slot := ⟨index-replyTileStart tiles lane reply retries tiles,hi⟩
      rw [List.getElem?_append_left (by simpa only [outputWriteEvents,List.length_cons,List.length_nil] using hi)] at he
      have hs := output_write_event_at lane (replyCheckpoint tiles lane reply retries).2 slot
      rw [hs] at he
      cases he
      have hh := Prod.mk.inj (Option.some.inj hw)
      exact ⟨slot,by dsimp [slot]; omega,hh.1.symm.trans (output_write_address lane slot),hh.2.symm⟩
    · rw [List.getElem?_append_right (by simpa only [outputWriteEvents,List.length_cons,List.length_nil] using
        (show 4 ≤ index-replyTileStart tiles lane reply retries tiles by omega))] at he
      have hm := List.mem_filterMap.mpr ⟨event,List.mem_of_getElem? he,hw⟩
      rw [return_no_global_write] at hm
      cases hm

theorem retry_source_indexed_footprint {tiles initial candidate id base size} (family : ReplySourceFamily tiles candidate)
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hf : (Access.kind Tma.localShared Access.globalDescriptor candidate.view (.tma (.source id))).bind
      Ptx.Event.Kind.footprint = some (base,size)) :
    ∃ lane slot, id = family.storeId lane slot ∧ base = ⟨.global,outputWordAddress (lane,slot)⟩ ∧ size = 4 := by
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
    obtain ⟨trace,ht,hid,_⟩ := Unified.eventAt_trace hr
    obtain ⟨lane,hlane⟩ := HopperStage.ctx_covered (hw.2.2.1 trace ht).1
    change (ctx tiles lane).id = trace.id at hlane
    have hthread : id.thread = (ctx tiles lane).id := (hlane.trans hid).symm
    have hh := Unified.eventAt_of_member hw.2.1 (family.members lane) (serial := id.serial)
    rw [family.ids lane,family.events lane] at hh
    have hget : (replyPositiveEvents tiles lane (family.replies lane) (family.schedules lane))[id.serial]? = some rich := by
      rw [← hh]
      have heq : (⟨(ctx tiles lane).id,id.serial⟩ : Ptx.Event.EventId) = id := by cases id; simp_all
      rw [heq]; exact hr
    obtain ⟨slot,hserial,haddress,hbytes⟩ := reply_complete_global_write_case hget hwrite
    refine ⟨lane,slot,?_,?_,?_⟩
    · cases id with | mk thread serial => exact congrArg₂ Ptx.Event.EventId.mk hthread hserial
    · cases base with | mk space address => exact congrArg₂ Location.mk hspace haddress
    · rw [hsize,hbytes,Symbolic.encode_length]; rfl

theorem retry_global_writer_metadata {tiles initial candidate writer loc value} (family : ReplySourceFamily tiles candidate)
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hg : loc.space = .global) (hwrite : Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer loc = some value) :
    ∃ lane slot, writer = .base (.tma (.source (family.storeId lane slot))) ∧
      outputWordAddress (lane,slot) ≤ loc.address ∧ loc.address < outputWordAddress (lane,slot)+4 := by
  obtain ⟨id,rfl⟩ := candidate_global_writer_is_source hb hw hc hg hwrite
  obtain ⟨base,size,hf⟩ := Unified.access_footprint_exists (.inr (by rw [hwrite]; rfl))
  obtain ⟨lane,slot,rfl,rfl,rfl⟩ := retry_source_indexed_footprint family hb hw hc hf
  have hr := Unified.access_footprint_bounds (.inr (by rw [hwrite]; rfl)) hf
  exact ⟨lane,slot,rfl,hr.2.1,hr.2.2⟩

theorem retry_global_unique_writers {tiles initial candidate loc left right lv rv} (family : ReplySourceFamily tiles candidate)
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hg : loc.space = .global) (hl : Unified.writeByte Tma.localShared Access.globalDescriptor candidate left loc = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor candidate right loc = some rv) : left = right := by
  obtain ⟨ll,ls,rfl,hleft⟩ := retry_global_writer_metadata family hb hw hc hg hl
  obtain ⟨rl,rs,rfl,hright⟩ := retry_global_writer_metadata family hb hw hc hg hr
  have he : outputWordAddress (ll,ls) = outputWordAddress (rl,rs) := by dsimp [outputWordAddress] at hleft hright ⊢; omega
  have ho := (output_byte_unique (left := (ll,ls)) (right := (rl,rs)) (i := 0) (j := 0)
    (by simpa only [outputByteAddress,Fin.val_zero,Nat.add_zero] using he)).1
  have hlanes := congrArg Prod.fst ho
  have hslots := congrArg Prod.snd ho
  cases hlanes
  cases hslots
  rfl

theorem retry_actual_output_byte {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    Unified.writeByte Tma.localShared Access.globalDescriptor candidate (.base (.tma (.source (family.storeId lane slot))))
      ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      some (.realPart .f32 ((replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).2 slot) index.val) := by
  have he : Access.kind Tma.localShared Access.globalDescriptor candidate.view (.tma (.source (family.storeId lane slot))) =
      some (.write ⟨.global,outputWordAddress (lane,slot)⟩
        (Symbolic.encode .f32 ((replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).2 slot))) := by
    simp only [Access.kind,Unified.view_eventAt,family_store_event family hw,Option.map_some,
      outputWriteEvent,Unified.eventView,Option.bind_some,output_write_address]
    rfl
  rw [Unified.base_write_preserved,Access.writeByte,he,Option.bind_some,Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte_offset]
  simp only [Symbolic.encode,Symbolic.Format.bytes,List.getElem?_map,List.getElem?_range index.isLt,Option.map_some]

end
end Ptx.Kernels.HopperDoubleBuffer
