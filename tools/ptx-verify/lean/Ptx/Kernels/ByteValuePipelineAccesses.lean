import Ptx.Kernels.ByteValuePipeline
import Ptx.Hopper.ByteSourceFootprints

/-! Actual access inventory, complete footprints and event readiness for the
generated store/load source, retaining arbitrary parameter and oracle values.
-/
namespace Ptx.Kernels.ByteValuePipeline
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def demands (mode : Ptx.Async.Mode) := ByteAuthority.Footprint.span base 4 mode

theorem writer_byte_at (value reply : Nat) (offset : Fin 4) :
    ByteContents.writeByte (candidate value reply) writerMemory (base.add offset.val) =
      some ((payload value)[offset.val]'(by simpa [payload] using offset.isLt)) := by
  change Ptx.Event.payloadByte base (payload value) (base.add offset.val) = _
  rw [Ptx.Event.payloadByte_offset]
  exact List.getElem?_eq_getElem (by simpa [payload] using offset.isLt)

theorem reader_byte_at (value reply : Nat) (offset : Fin 4) :
    ByteContents.readByte (candidate value reply) readerMemory (base.add offset.val) =
      some ((payload reply)[offset.val]'(by simpa [payload] using offset.isLt)) := by
  change Ptx.Event.payloadByte base (payload reply) (base.add offset.val) = _
  rw [Ptx.Event.payloadByte_offset]
  exact List.getElem?_eq_getElem (by simpa [payload] using offset.isLt)

theorem no_tma_copy (value reply : Nat) (id : Tma.CopyId) : Tma.copyAt (candidate value reply).view id = none := by
  unfold Tma.copyAt
  rw [Unified.view_eventAt]
  cases he : (candidate value reply).eventAt id.issue with
  | none => rfl
  | some event =>
    rcases source_event_shape he with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rfl

theorem no_nonbulk_copy (value reply : Nat) (id : Ptx.Event.EventId) : Access.copyAt (candidate value reply).view id = none := by
  unfold Access.copyAt
  rw [Unified.view_eventAt]
  cases he : (candidate value reply).eventAt id with
  | none => rfl
  | some event =>
    rcases source_event_shape he with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rfl

theorem no_native_representative (value reply : Nat) (id : Ptx.Event.EventId) : (candidate value reply).representativeAt id = none := by
  unfold Unified.Candidate.representativeAt Unified.Candidate.wgmmaAt
  cases he : (candidate value reply).eventAt id with
  | none => rfl
  | some event =>
    rcases source_event_shape he with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rfl

theorem writer_only {value reply memory loc byteValue}
    (hw : ByteContents.writeByte (candidate value reply) memory loc = some byteValue) : memory = writerMemory := by
  cases memory with
  | wgmmaRead issue operand => simp [ByteContents.writeByte,Unified.native_write_none] at hw
  | base node =>
    cases node with
    | copyRead id | copyWrite id =>
      simp [ByteContents.writeByte,Unified.writeByte,Unified.kind,Access.kind,no_nonbulk_copy] at hw
    | tma node =>
      cases node with
      | source id =>
        cases he : (candidate value reply).eventAt id with
        | none => simp [ByteContents.writeByte,Unified.writeByte,Unified.kind,Access.kind,Unified.view_eventAt,he] at hw
        | some event =>
          rcases source_event_shape he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · rfl
          · cases hw
      | descriptor id | read id offset | write id offset | notify id =>
        simp [ByteContents.writeByte,Unified.writeByte,Unified.kind,Access.kind,no_tma_copy,Tma.readLocation,Tma.writeLocation,Tma.transferByte] at hw

theorem reader_only {value reply memory loc byteValue}
    (hr : ByteContents.readByte (candidate value reply) memory loc = some byteValue) : memory = readerMemory := by
  cases memory with
  | wgmmaRead issue operand => simp [ByteContents.readByte,Unified.readByte,Unified.kind,no_native_representative] at hr
  | base node =>
    cases node with
    | copyRead id | copyWrite id =>
      simp [ByteContents.readByte,Unified.readByte,Unified.kind,Access.kind,no_nonbulk_copy] at hr
    | tma node =>
      cases node with
      | source id =>
        cases he : (candidate value reply).eventAt id with
        | none => simp [ByteContents.readByte,Unified.readByte,Unified.kind,Access.kind,Unified.view_eventAt,he] at hr
        | some event =>
          rcases source_event_shape he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · cases hr
          · rfl
      | descriptor id | read id offset | write id offset | notify id =>
        simp [ByteContents.readByte,Unified.readByte,Unified.kind,Access.kind,no_tma_copy,Tma.readLocation,Tma.writeLocation,Tma.transferByte] at hr

theorem writer_ready (value reply : Nat) : ByteAuthority.Ready .one (candidate value reply) (fun _ => []) (fun _ => False) writerControl := by
  refine ⟨by simp [Present,Tma.Present,Hopper.Candidate.Present,writerControl,writer_view],by simp,?_⟩
  intro before he
  obtain ⟨earlier,_,hp⟩ := ByteContents.ordinary_source_predecessors (writer_lookup value reply) (by intro _ _ h; cases h) he
  exact (Nat.not_lt_zero _ hp.2.2.2).elim

theorem reader_predecessor {value reply before}
    (he : Unified.ControlEdge .one (candidate value reply) (fun _ => []) before readerControl) : before = writerControl := by
  obtain ⟨earlier,rfl,hp⟩ := ByteContents.ordinary_source_predecessors (reader_lookup value reply) (by intro _ _ h; cases h) he
  have hs : earlier.serial = 0 := by have hb := hp.2.2.2; change earlier.serial < 1 at hb; omega
  have hi : earlier.thread = thread := hp.2.2.1
  have hid : earlier = writer := by cases earlier; simp_all [writer]
  rw [hid]
  rfl

theorem reader_ready_after_writer (value reply : Nat) :
    ByteAuthority.Ready .one (candidate value reply) (fun _ => []) (fun n => False ∨ n = writerControl) readerControl := by
  refine ⟨by simp [Present,Tma.Present,Hopper.Candidate.Present,readerControl,reader_view],?_,?_⟩
  · rintro (h | h)
    · exact h
    · cases h
  · intro before he
    exact Or.inr (reader_predecessor he)

theorem footprint_distinct (mode : Ptx.Async.Mode) : ByteAuthority.Footprint.Distinct (demands mode) := ByteAuthority.Footprint.span_distinct _ _ _

theorem writer_footprint_sound (value reply : Nat) : ByteAuthority.Footprint.Sound (candidate value reply) writerControl (demands .write) := by
  intro demand hm
  obtain ⟨offset,rfl⟩ := List.mem_ofFn.mp hm
  have hb : offset.val < (payload value).length := by simpa [payload] using offset.isLt
  refine ⟨.kernel,.kernel (.write (value := (payload value)[offset.val]) (writer_view value reply) ?_)⟩
  change Ptx.Event.payloadByte base (payload value) (base.add offset.val) = _
  rw [Ptx.Event.payloadByte_offset]
  exact List.getElem?_eq_getElem hb

theorem reader_footprint_sound (value reply : Nat) : ByteAuthority.Footprint.Sound (candidate value reply) readerControl (demands .read) := by
  intro demand hm
  obtain ⟨offset,rfl⟩ := List.mem_ofFn.mp hm
  have hb : offset.val < (payload reply).length := by simpa [payload] using offset.isLt
  refine ⟨.kernel,.kernel (.read (value := (payload reply)[offset.val]) (reader_view value reply) ?_)⟩
  change Ptx.Event.payloadByte base (payload reply) (base.add offset.val) = _
  rw [Ptx.Event.payloadByte_offset]
  exact List.getElem?_eq_getElem hb

theorem writer_footprint_covers (value reply : Nat) : ByteAuthority.Footprint.Covers (candidate value reply) writerControl (demands .write) := by
  intro loc mode hu
  have hx := ByteAuthority.Footprint.ordinary_source_uses (writer_view value reply) hu
  cases mode with
  | read => obtain ⟨_,h⟩ := hx; cases h
  | write =>
    obtain ⟨v,hv⟩ := hx
    have hb := Ptx.Event.payloadByte_bounds hv
    have hl : loc.space = base.space ∧ base.address ≤ loc.address ∧ loc.address < base.address+4 := ⟨hb.1.symm,by simpa [payload] using hb.2⟩
    let offset : Fin 4 := ⟨loc.address-base.address,by omega⟩
    refine ⟨⟨base.add offset.val,.write⟩,ByteAuthority.Footprint.span_member _ _ _ offset,?_,ByteAuthority.authorizes_self _⟩
    cases loc with
    | mk space address =>
      simp only [Location.add,Location.mk.injEq]
      refine ⟨hl.1.symm,?_⟩
      have hlo : base.address ≤ address := hl.2.1
      change base.address+(address-base.address) = address
      omega

theorem reader_footprint_covers (value reply : Nat) : ByteAuthority.Footprint.Covers (candidate value reply) readerControl (demands .read) := by
  intro loc mode hu
  have hx := ByteAuthority.Footprint.ordinary_source_uses (reader_view value reply) hu
  cases mode with
  | write => obtain ⟨_,h⟩ := hx; cases h
  | read =>
    obtain ⟨v,hv⟩ := hx
    have hb := Ptx.Event.payloadByte_bounds hv
    have hl : loc.space = base.space ∧ base.address ≤ loc.address ∧ loc.address < base.address+4 := ⟨hb.1.symm,by simpa [payload] using hb.2⟩
    let offset : Fin 4 := ⟨loc.address-base.address,by omega⟩
    refine ⟨⟨base.add offset.val,.read⟩,ByteAuthority.Footprint.span_member _ _ _ offset,?_,ByteAuthority.authorizes_self _⟩
    cases loc with
    | mk space address =>
      simp only [Location.add,Location.mk.injEq]
      refine ⟨hl.1.symm,?_⟩
      have hlo : base.address ≤ address := hl.2.1
      change base.address+(address-base.address) = address
      omega

end
end Ptx.Kernels.ByteValuePipeline
