import Ptx.Kernels.HopperDoubleBufferCausalWitness

/-! Actual writers at one byte are equal or byte-ordered. Shared bytes use
their real tile/operand owner; overlapping output words recover the same
source thread from the checked output layout. No global unique-writer or
already-coherent memory premise is used. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_shared_writers_order {a b tiles loc left right lv rv} (hb : tiles ≤ 2^28) (hs : loc.space = .shared .zero)
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) left loc = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) right loc = some rv) :
    left = right ∨ Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster loc left right ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) (dataHistories a b tiles) dataCluster loc right left := by
  obtain ⟨id,offset,_,hloc⟩ := data_shared_writer_is_tensor hs hl
  obtain ⟨tile,ht,hregion⟩ := data_tensor_write_region hb hloc
  rcases hregion with ⟨_,ho,hbase⟩ | ⟨_,ho,hbase⟩
  · let owner := Wgmma.aByteOwner ⟨offset,ho⟩
    have hnative : dataNativeLocation a b tiles tile (.a owner.1 owner.2) = loc := by
      rw [data_native_a_location]
      change (⟨.shared .zero,aBase (stage tile)+(Wgmma.aOffset (Wgmma.aByteOwner ⟨offset,ho⟩)).val⟩ : Location) = loc
      rw [Wgmma.a_offset_owner]
      exact hbase.symm
    have hc := data_native_writers_comparable (tile := tile) (operand := .a owner.1 owner.2) hb
      (by rw [hnative]; exact hl) (by rw [hnative]; exact hr)
    rwa [hnative] at hc
  · let owner := Wgmma.bByteOwner ⟨offset,ho⟩
    have hnative : dataNativeLocation a b tiles tile (.b owner.1 owner.2) = loc := by
      rw [data_native_b_location]
      change (⟨.shared .zero,bBase (stage tile)+(Wgmma.bOffset (Wgmma.bByteOwner ⟨offset,ho⟩)).val⟩ : Location) = loc
      rw [Wgmma.b_offset_owner]
      exact hbase.symm
    have hc := data_native_writers_comparable (tile := tile) (operand := .b owner.1 owner.2) hb
      (by rw [hnative]; exact hl) (by rw [hnative]; exact hr)
    rwa [hnative] at hc

theorem data_global_writer_source {a b tiles writer loc value} (hb : tiles ≤ 2^28) (hg : loc.space = .global)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) writer loc = some value) :
    ∃ id, writer = .base (.tma (.source id)) := by
  cases writer with
  | wgmmaRead issue operand => rw [Unified.native_write_none] at hw; cases hw
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.writeByte,Unified.kind,Access.kind,data_no_nonbulk] at hw
    | tma node =>
      cases node with
      | source id => exact ⟨id,rfl⟩
      | descriptor id => rw [Unified.base_write_preserved,Access.descriptor_no_write] at hw; cases hw
      | read id offset => rw [Unified.base_write_preserved,Access.tensor_read_no_write] at hw; cases hw
      | notify id => cases hw
      | write id offset =>
        have hl := Access.tensor_write_access (.inr (by rw [← Unified.base_write_preserved,hw]; rfl))
        obtain ⟨tile,ht,hregion⟩ := data_tensor_write_region hb hl
        rcases hregion with ⟨_,_,he⟩ | ⟨_,_,he⟩
        all_goals have hs := congrArg Location.space he
        all_goals rw [hg] at hs
        all_goals cases hs

theorem data_source_writer_present {a b tiles id loc value}
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) (.base (.tma (.source id))) loc = some value) :
    (dataCompleteCandidate a b tiles).view.Present id := by
  cases he : (dataCompleteCandidate a b tiles).view.eventAt id with
  | none => simp [Unified.writeByte,Unified.kind,Access.kind,he] at hw
  | some event => simp only [Hopper.Candidate.Present,he,Option.isSome_some]

theorem data_global_writer_threads_equal {a b tiles left right loc lv rv}
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) (.base (.tma (.source left))) loc = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) (.base (.tma (.source right))) loc = some rv) :
    left.thread = right.thread := by
  obtain ⟨lb,ls,hfl⟩ := Unified.access_footprint_exists (.inr (by rw [hl]; rfl))
  obtain ⟨rb,rs,hfr⟩ := Unified.access_footprint_exists (.inr (by rw [hr]; rfl))
  obtain ⟨ll,li,htl,hbl,hsl⟩ := data_source_footprint_owner hfl
  obtain ⟨rl,ri,htr,hbr,hsr⟩ := data_source_footprint_owner hfr
  have hleft := Unified.access_footprint_bounds (.inr (by rw [hl]; rfl)) hfl
  have hright := Unified.access_footprint_bounds (.inr (by rw [hr]; rfl)) hfr
  rw [hbl,hsl] at hleft
  rw [hbr,hsr] at hright
  have hword : outputWordAddress (ll,li) = outputWordAddress (rl,ri) := by
    dsimp only [outputWordAddress] at hleft hright ⊢
    omega
  have howner := (output_byte_unique (left := (ll,li)) (right := (rl,ri)) (i := 0) (j := 0)
    (by simpa only [outputByteAddress,Fin.val_zero,Nat.add_zero] using hword)).1
  have hlanes := congrArg Prod.fst howner
  cases hlanes
  exact htl.trans htr.symm

theorem data_global_writers_order {a b tiles loc left right lv rv} (hb : tiles ≤ 2^28) (hg : loc.space = .global)
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) left loc = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) right loc = some rv) :
    left = right ∨ Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster loc left right ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) (dataHistories a b tiles) dataCluster loc right left := by
  obtain ⟨lid,rfl⟩ := data_global_writer_source hb hg hl
  obtain ⟨rid,rfl⟩ := data_global_writer_source hb hg hr
  have hthreads := data_global_writer_threads_equal hl hr
  rcases lt_trichotomy lid.serial rid.serial with hlt | heq | hgt
  · right; left
    apply Unified.base_byte_order
    exact .single (.inl (.inl ⟨data_source_writer_present hl,data_source_writer_present hr,hthreads,hlt⟩))
  · have hid : lid = rid := by cases lid; cases rid; cases hthreads; cases heq; rfl
    cases hid
    exact Or.inl rfl
  · right; right
    apply Unified.base_byte_order
    exact .single (.inl (.inl ⟨data_source_writer_present hr,data_source_writer_present hl,hthreads.symm,hgt⟩))

theorem data_all_writers_order {a b tiles loc left right lv rv} (hb : tiles ≤ 2^28)
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) left loc = some lv)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) right loc = some rv) :
    left = right ∨ Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster loc left right ∨
      Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) (dataHistories a b tiles) dataCluster loc right left := by
  obtain ⟨base,size,hf,hs | hg⟩ := data_write_footprint_regions hb hl
  all_goals have hbound := Unified.access_footprint_bounds (.inr (by rw [hl]; rfl)) hf
  · exact data_shared_writers_order hb (hbound.1.symm.trans hs.1) hl hr
  · exact data_global_writers_order hb (hbound.1.symm.trans hg.1) hl hr

end
end Ptx.Kernels.HopperDoubleBuffer
