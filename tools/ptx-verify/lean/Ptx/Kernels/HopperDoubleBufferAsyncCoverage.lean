import Ptx.Kernels.HopperDoubleBufferAsyncBindings
import Ptx.Kernels.HopperDoubleBufferRetryMemoryGeometry
import Ptx.Kernels.HopperDoubleBufferRetryNativeCases

/-! Exhaustive positive-K coverage of every actual Progress.Use, with no
caller-supplied selected-work scope. Ordinary/resource source accesses remain
outside Progress.Use and are not claimed protected by this certificate. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

theorem native_representative_tile {tiles initial candidate issue mark call}
    (family : ReplySourceFamily tiles candidate) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hr : candidate.representativeAt issue = some (mark,call)) :
    ∃ tile, tile < tiles ∧ issue = family.mmaId tile 0 := by
  obtain ⟨tile,lane,ht,hid,_,hcall⟩ := retry_native_mma_case family hw (Unified.representative_at hr).1
  have hl := congrArg (fun call => call.lane.val) hcall
  have hf : (family.calls tile lane).lane = lane := (familyCollective family hw tile ht).cohort.lane lane
  rw [hf] at hl
  have hzero : lane = 0 := Fin.ext (hl.symm.trans (Unified.representative_at hr).2)
  subst lane
  exact ⟨tile,ht,hid.trans (retry_native_mma_id family tile 0)⟩

theorem async_use_work_case {tiles initial candidate work control node loc mode}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hu : Use Tma.localShared Access.globalDescriptor candidate work control node loc mode) :
    ∃ tile, tile < tiles ∧ (work = .tma (family.copyAId tile) ∨ work = .tma (family.copyBId tile) ∨ work = .native (family.mmaId tile 0)) := by
  have hcopy : ∀ id op, Tma.copyAt candidate.view id = some op →
      ∃ tile, tile < tiles ∧ (id = family.copyAId tile ∨ id = family.copyBId tile) := by
    intro id op hc
    obtain ⟨tile,hp,ha | hb⟩ := retry_all_source_copies family ht hw id op hc
    · exact ⟨tile,hp,.inl ha.1⟩
    · exact ⟨tile,hp,.inr hb.1⟩
  cases hu with
  | descriptor hc ho =>
    obtain ⟨tile,hp,ha | hb⟩ := hcopy _ _ hc
    · exact ⟨tile,hp,.inl (congrArg Work.tma ha)⟩
    · exact ⟨tile,hp,.inr (.inl (congrArg Work.tma hb))⟩
  | tmaRead hl hv =>
    obtain ⟨op,hc,_⟩ := Tma.read_has_copy (by rw [hl]; rfl)
    obtain ⟨tile,hp,ha | hb⟩ := hcopy _ _ hc
    · exact ⟨tile,hp,.inl (congrArg Work.tma ha)⟩
    · exact ⟨tile,hp,.inr (.inl (congrArg Work.tma hb))⟩
  | tmaWrite hl hv =>
    obtain ⟨op,hc,_⟩ := Tma.write_has_copy (location_write_present hl)
    obtain ⟨tile,hp,ha | hb⟩ := hcopy _ _ hc
    · exact ⟨tile,hp,.inl (congrArg Work.tma ha)⟩
    · exact ⟨tile,hp,.inr (.inl (congrArg Work.tma hb))⟩
  | nativeRead hr =>
    obtain ⟨tile,hp,hi⟩ := native_representative_tile family hw hr
    exact ⟨tile,hp,.inr (.inr (congrArg Work.native hi))⟩

theorem all_async_region_coverage {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) :
    Regions.Covers Tma.localShared Access.globalDescriptor candidate (fun _ => True) (asyncBindings family) := by
  intro work control node loc mode _ hu
  obtain ⟨tile,hp,ha | hb' | hn⟩ := async_use_work_case family ht hw hu
  · subst work
    have hc := Regions.covers_rename (tma_a_region_coverage family hw hd hb tile hp) (aBuffers tile) (ticketShift (6*tile))
    obtain ⟨binding,hmem,hwork,hmode,hregion⟩ := hc _ _ _ _ _ rfl hu
    refine ⟨binding,List.mem_flatMap.mpr ⟨tile,List.mem_range.mpr hp,?_⟩,hwork,hmode,hregion⟩
    simp only [tileAsyncBindings,List.mem_append]
    exact .inl (.inl hmem)
  · subst work
    have hc := Regions.covers_rename (tma_b_region_coverage family hw hd hb tile hp) (bBuffers tile) (ticketShift (6*tile+2))
    obtain ⟨binding,hmem,hwork,hmode,hregion⟩ := hc _ _ _ _ _ rfl hu
    refine ⟨binding,List.mem_flatMap.mpr ⟨tile,List.mem_range.mpr hp,?_⟩,hwork,hmode,hregion⟩
    simp only [tileAsyncBindings,List.mem_append]
    exact .inl (.inr hmem)
  · subst work
    have hc := Regions.covers_rename (native_region_coverage family hw tile hp) (nativeBuffers tile) (ticketShift (6*tile+4))
    obtain ⟨binding,hmem,hwork,hmode,hregion⟩ := hc _ _ _ _ _ rfl hu
    refine ⟨binding,List.mem_flatMap.mpr ⟨tile,List.mem_range.mpr hp,?_⟩,hwork,hmode,hregion⟩
    simp only [tileAsyncBindings,List.mem_append]
    exact .inr hmem

theorem completed_async_region_certificate {tiles initial candidate}
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) :
    ∃ family : ReplySourceFamily tiles candidate,
      Regions.Separated (asyncLayout tiles) ∧ Regions.Mapped (asyncLayout tiles) (asyncPlan family) (asyncBindings family) ∧
        Regions.Covers Tma.localShared Access.globalDescriptor candidate (fun _ => True) (asyncBindings family) := by
  obtain ⟨family⟩ := completed_candidate_reply_family ht hb hw hc
  exact ⟨family,async_layout_separated tiles,async_bindings_mapped family,all_async_region_coverage family ht hb hw hd⟩

end
end Ptx.Kernels.HopperDoubleBuffer
