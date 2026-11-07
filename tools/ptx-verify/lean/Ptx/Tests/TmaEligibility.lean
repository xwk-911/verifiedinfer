import Ptx.Hopper.ByteVisibility
import Ptx.Hopper.AccessInversion
import Ptx.Tests.TmaPublication

/-! Race freedom and derived read eligibility for every reply in the actual
TMA publication source family. No selected rf/co, oracle value or race-freedom
premise is used by the byte-conflict classification. -/
namespace Ptx.TmaEligibilityTests
open Ptx.ISA Ptx.Hopper
open Ptx.TmaPublicationTests (candidate events bytes trace eid histories cluster)
open Ptx.TmaTests (view copy operation)
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 500000

def ordinaryKind : Hopper.Event → Option Scalar.Kind
  | .ampere (.ordinary k) => some k
  | _ => none

theorem source_memory_id {n event k}
    (hk : Access.kind Tma.localShared Access.globalDescriptor (candidate n) (.tma (.source event)) = some k) :
    (event = eid 5 ∧ k = .read ⟨.shared .zero,16⟩ (bytes n)) ∨
    (event = eid 6 ∧ k = .write ⟨.global,8192⟩ (bytes n)) := by
  cases he : (candidate n).eventAt event with
  | none => simp [Access.kind,he] at hk
  | some e =>
    obtain ⟨t,ht,hid,hg⟩ := Ptx.Hopper.eventAt_trace he
    have ht : t = trace n := List.mem_singleton.mp ht
    subst t
    have hb : event.serial < 8 := (List.getElem?_eq_some_iff.mp hg).1
    have hid : event.thread = TmaTests.id := hid.symm
    have hall : ∀ index : Fin 8, ∀ actual,
        (events n)[index.val]? = some actual →
        ordinaryKind actual = some k →
        (index.val = 5 ∧ k = .read ⟨.shared .zero,16⟩ (bytes n)) ∨
        (index.val = 6 ∧ k = .write ⟨.global,8192⟩ (bytes n)) := by
      intro index actual hget hkind
      fin_cases index <;> simp only [events,List.getElem?_cons_zero,List.getElem?_cons_succ] at hget
      all_goals cases hget
      all_goals simp only [ordinaryKind] at hkind
      all_goals cases hkind
      all_goals first | exact .inl ⟨rfl,rfl⟩ | exact .inr ⟨rfl,rfl⟩
    have hkind : ordinaryKind e = some k := by
      change ((candidate n).eventAt event).bind (fun actual => match actual with
        | .ampere (.ordinary actualKind) => some actualKind | _ => none) = some k at hk
      rw [he] at hk
      exact hk
    rcases hall ⟨event.serial,hb⟩ e hg hkind with ⟨hs,hk⟩ | ⟨hs,hk⟩
    · exact .inl ⟨by cases event with | mk thread serial => exact congrArg₂ Ptx.Event.EventId.mk hid hs,hk⟩
    · exact .inr ⟨by cases event with | mk thread serial => exact congrArg₂ Ptx.Event.EventId.mk hid hs,hk⟩

theorem write_inventory {n writer loc value}
    (hw : Access.writeByte Tma.localShared Access.globalDescriptor (candidate n) writer loc = some value) :
    (writer = .tma (.source (eid 6)) ∧ loc.space = .global ∧ 8192 ≤ loc.address ∧ loc.address < 8196) ∨
    (writer = .tma (.write operation (loc.address-16)) ∧ loc.space = .shared .zero ∧ 16 ≤ loc.address ∧ loc.address < 48) := by
  have ha : Access.Accesses Tma.localShared Access.globalDescriptor (candidate n) writer loc := .inr (by rw [hw]; rfl)
  obtain ⟨k,hk⟩ := Access.access_kind ha
  cases writer with
  | copyRead issue | copyWrite issue => simp [Access.kind,TmaPublicationTests.no_nonbulk] at hk
  | tma node =>
    cases node with
    | source event =>
      rcases source_memory_id hk with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · simp [Access.writeByte,hk,Ptx.Event.Kind.writeByte] at hw
      · have hb := Access.access_bounds ha (show (Access.kind Tma.localShared Access.globalDescriptor (candidate n) _).bind
            Ptx.Event.Kind.footprint = some (⟨.global,8192⟩,4) by simp [hk,Ptx.Event.Kind.footprint,bytes])
        exact .inl ⟨rfl,hb.1.symm,hb.2⟩
    | descriptor id => rw [Access.descriptor_no_write] at hw; cases hw
    | read id offset => rw [Access.tensor_read_no_write] at hw; cases hw
    | notify id => cases hw
    | write actual offset =>
      have hl := Access.tensor_write_access ha
      cases hc : Tma.copyAt (candidate n) actual with
      | none => simp [Tma.writeLocation,hc] at hl
      | some op =>
        obtain ⟨rfl,rfl⟩ := TmaPublicationTests.only_copy hc
        simp only [Tma.writeLocation,hc,Option.bind_some] at hl
        split at hl
        · rename_i ho
          have he : (⟨.shared .zero,16+offset⟩ : Location) = loc := Option.some.inj hl
          have hs := congrArg Location.space he
          have had := congrArg Location.address he
          change offset < 32 at ho
          exact .inr ⟨TmaPublicationTests.unique_shared_writer hs.symm hw,hs.symm,by simp only at had; omega,by simp only at had; omega⟩
        · cases hl

theorem shared_access_inventory {n node loc}
    (ha : Access.Accesses Tma.localShared Access.globalDescriptor (candidate n) node loc)
    (hs : loc.space = .shared .zero) :
    (node = .tma (.source (eid 5)) ∧ 16 ≤ loc.address ∧ loc.address < 20) ∨
    node = .tma (.write operation (loc.address-16)) := by
  obtain ⟨k,hk⟩ := Access.access_kind ha
  cases node with
  | copyRead issue | copyWrite issue => simp [Access.kind,TmaPublicationTests.no_nonbulk] at hk
  | tma node =>
    cases node with
    | source event =>
      rcases source_memory_id hk with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · have hb := Access.access_bounds ha (show (Access.kind Tma.localShared Access.globalDescriptor (candidate n) _).bind
            Ptx.Event.Kind.footprint = some (⟨.shared .zero,16⟩,4) by simp [hk,Ptx.Event.Kind.footprint,bytes])
        exact .inl ⟨rfl,hb.2⟩
      · have hb := Access.access_bounds ha (show (Access.kind Tma.localShared Access.globalDescriptor (candidate n) _).bind
            Ptx.Event.Kind.footprint = some (⟨.global,8192⟩,4) by simp [hk,Ptx.Event.Kind.footprint,bytes])
        simp [hs] at hb
    | descriptor actual =>
      cases hc : Tma.copyAt (candidate n) actual with
      | none => simp [Access.kind,hc] at hk
      | some op =>
        obtain ⟨rfl,rfl⟩ := TmaPublicationTests.only_copy hc
        have hb := Access.access_bounds ha (show (Access.kind Tma.localShared Access.globalDescriptor (candidate n) _).bind
          Ptx.Event.Kind.footprint = some (⟨.global,4096⟩,128) by simp [Access.kind,hc,Access.globalDescriptor,Ptx.Event.Kind.footprint,TensorMap.encode_length]; rfl)
        simp [hs] at hb
    | read actual offset =>
      have hl := Access.tensor_read_access ha
      obtain ⟨op,hc,_⟩ := Tma.read_has_copy (by rw [hl]; rfl)
      have hsrc : Tma.sourceByte op.descriptor op.coordinates offset = some loc := by simpa [Tma.readLocation,hc] using hl
      have hb := (Tma.source_byte_some hsrc).2.2.1
      simp [hs] at hb
    | write actual offset =>
      obtain ⟨location,value,hl,hv,rfl⟩ := Access.tensor_write_shape hk
      have hwrite : Access.writeByte Tma.localShared Access.globalDescriptor (candidate n) (.tma (.write actual offset)) loc =
          some value := by
        have he : location = loc := Option.some.inj (hl.symm.trans (Access.tensor_write_access ha))
        cases he
        exact Access.tensor_write hl hv
      exact .inr (TmaPublicationTests.unique_shared_writer hs hwrite)
    | notify id => simp [Access.kind] at hk

theorem output_access_inventory {n node loc}
    (ha : Access.Accesses Tma.localShared Access.globalDescriptor (candidate n) node loc)
    (hs : loc.space = .global) (hlo : 8192 ≤ loc.address) : node = .tma (.source (eid 6)) := by
  obtain ⟨k,hk⟩ := Access.access_kind ha
  cases node with
  | copyRead issue | copyWrite issue => simp [Access.kind,TmaPublicationTests.no_nonbulk] at hk
  | tma node =>
    cases node with
    | source event =>
      rcases source_memory_id hk with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · have hb := Access.access_bounds ha (show (Access.kind Tma.localShared Access.globalDescriptor (candidate n) _).bind
            Ptx.Event.Kind.footprint = some (⟨.shared .zero,16⟩,4) by simp [hk,Ptx.Event.Kind.footprint,bytes])
        simp [hs] at hb
      · rfl
    | descriptor actual =>
      cases hc : Tma.copyAt (candidate n) actual with
      | none => simp [Access.kind,hc] at hk
      | some op =>
        obtain ⟨rfl,rfl⟩ := TmaPublicationTests.only_copy hc
        have hb := Access.access_bounds ha (show (Access.kind Tma.localShared Access.globalDescriptor (candidate n) _).bind
          Ptx.Event.Kind.footprint = some (⟨.global,4096⟩,128) by simp [Access.kind,hc,Access.globalDescriptor,Ptx.Event.Kind.footprint,TensorMap.encode_length]; rfl)
        simp only at hb
        omega
    | read actual offset =>
      have hl := Access.tensor_read_access ha
      obtain ⟨op,hc,_⟩ := Tma.read_has_copy (by rw [hl]; rfl)
      have hsrc : Tma.sourceByte op.descriptor op.coordinates offset = some loc := by simpa [Tma.readLocation,hc] using hl
      obtain ⟨rfl,rfl⟩ := TmaPublicationTests.only_copy hc
      have hb := Tma.source_in_global_span (show 0 < view.elementBytes by decide) hsrc
      change 128 ≤ loc.address ∧ loc.address < 672 at hb
      omega
    | write actual offset =>
      obtain ⟨location,value,hl,hv,rfl⟩ := Access.tensor_write_shape hk
      have he : location = loc := Option.some.inj (hl.symm.trans (Access.tensor_write_access ha))
      cases he
      have hw := Access.tensor_write (descriptor := Access.globalDescriptor) hl hv
      rcases write_inventory hw with ⟨hid,_⟩ | ⟨_,hspace,_⟩
      · cases hid
      · simp [hs] at hspace
    | notify id => simp [Access.kind] at hk

theorem ordered_conflicts (n : Nat) : ∀ writer other loc,
    Access.WritesAt Tma.localShared Access.globalDescriptor (candidate n) writer loc →
    Access.Accesses Tma.localShared Access.globalDescriptor (candidate n) other loc →
    writer = other ∨ Access.ByteOrder Tma.localShared Access.globalDescriptor (candidate n) histories cluster loc writer other ∨
      Access.ByteOrder Tma.localShared Access.globalDescriptor (candidate n) histories cluster loc other writer := by
  intro writer other loc hw ha
  obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hw
  rcases write_inventory hvalue with ⟨rfl,hs,hlo,_⟩ | ⟨hid,hs,hlo,_⟩
  · exact .inl (output_access_inventory ha hs hlo).symm
  · subst writer
    rcases shared_access_inventory ha hs with ⟨rfl,hleft,hright⟩ | hid
    · have ho : loc.address-16 < 4 := by omega
      have he : loc = (⟨.shared .zero,16+(loc.address-16)⟩ : Location) := by
        rcases loc with ⟨space,address⟩
        simp only at hs hleft
        simp only [Location.mk.injEq]
        exact ⟨hs,by omega⟩
      have hp := TmaPublicationTests.byte_published n ⟨loc.address-16,ho⟩
      have hh : Access.Published Tma.localShared (candidate n) histories cluster
          (.tma (.write operation (loc.address-16))) (.tma (.source (eid 5))) loc := by simpa only [← he] using hp
      exact .inr (.inl (Access.published_byte_order hh))
    · exact .inl hid.symm

theorem race_free (n : Nat) (rf : Access.ReadsFrom) :
    ∀ loc a b, ¬ Access.DataRaceAt Tma.localShared Access.globalDescriptor (candidate n) histories cluster rf loc a b :=
  Access.ordered_conflicts_no_races (ordered_conflicts n)

theorem eligible (n : Nat) (rf : Access.ReadsFrom) (read loc) :
    Access.Eligible Tma.localShared Access.globalDescriptor (candidate n) histories cluster rf read loc :=
  Access.race_free_eligible (race_free n rf) read loc

theorem consumer_word {n initial rf co}
    (hc : Access.CausalConstraints Tma.localShared Access.globalDescriptor (candidate n) initial rf co histories cluster) :
    wrap 32 n = TmaPublicationTests.answer :=
  TmaPublicationTests.consumer_word (Access.causality_visibility hc (eligible n rf (.tma (.source (eid 5))) ⟨.shared .zero,16⟩).1)
    (fun offset => eligible n rf _ _)

theorem zero_reply_inadmissible {initial rf co} :
    ¬ Access.CausalConstraints Tma.localShared Access.globalDescriptor (candidate 0) initial rf co histories cluster := by
  intro hc
  have hw := consumer_word hc
  exact (by decide : (0 : Nat) ≠ TmaPublicationTests.answer) hw

end
end Ptx.TmaEligibilityTests
