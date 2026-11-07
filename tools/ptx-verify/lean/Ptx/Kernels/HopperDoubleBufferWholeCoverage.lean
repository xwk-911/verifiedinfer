import Ptx.Kernels.HopperDoubleBufferWholeLoans

/-! Joint exact-mode coverage and pending guards. No selected TMA/native role
or pre-existing loan certificate is supplied by the public caller. -/
namespace Ptx.Kernels.HopperDoubleBuffer.Whole
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

abbrev Use (candidate : Unified.Candidate) := Progress.UnifiedUse Tma.localShared Access.globalDescriptor candidate

def Covers (candidate : Unified.Candidate) (bindings : List Regions.Binding) : Prop :=
  ∀ work control loc mode, Use candidate work control loc mode →
    ∃ binding ∈ bindings, binding.work = work ∧ binding.mode = mode ∧ binding.region.Contains loc

theorem all_uses_covered {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) :
    Covers candidate (bindings family) := by
  intro work control loc mode hu
  cases hu with
  | async hu =>
    obtain ⟨binding,hm,hwork,hmode,hregion⟩ := all_async_region_coverage family ht hb hw hd _ _ _ _ _ trivial hu
    exact ⟨binding,List.mem_append_left _ hm,hwork,hmode,hregion⟩
  | kernel hu =>
    obtain ⟨index,hmode,hregion⟩ := positive_kernel_use_coverage family ht hb hw hc hd _ _ _ hu
    change Fin 2 at index
    fin_cases index
    · exact ⟨(rootBindings tiles)[0]'(by simp [rootBindings]),List.mem_append_right _ (by simp [rootBindings]),rfl,hmode,hregion⟩
    · exact ⟨(rootBindings tiles)[1]'(by simp [rootBindings]),List.mem_append_right _ (by simp [rootBindings]),rfl,hmode,hregion⟩

theorem completed_use_done {block candidate histories cluster done work control loc mode}
    (hr : Reached block candidate histories done)
    (hc : Completed Tma.localShared candidate histories cluster done work)
    (hu : Use candidate work control loc mode) : done control := by
  cases hu with
  | async hu => exact reached_completed_use_done hr hc hu
  | kernel hu => exact completed_kernel_use_done hc hu

theorem public_pending_reclaim_write_rejected {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (values : List Nat) (hv : values.length = 10) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) {histories state work control loc mode target region}
    (hs : Bridge.Steps HopperStage.block Tma.localShared candidate histories dataCluster (plan family)
      ⟨prepared values tiles,fun _ => False⟩ state)
    (hu : Use candidate work control loc mode) (hp : ¬state.done control)
    (hl : layout tiles target = some region) (hcontains : region.Contains loc) :
    Ptx.Async.reclaim state.protocol target = .error .outstandingLoan ∧
      ∀ value, Ptx.Async.hostWrite state.protocol target value = .error .outstandingLoan := by
  obtain ⟨binding,hm,hwork,_,hregion⟩ := all_uses_covered family ht hb hw hc hd _ _ _ _ hu
  have hmap := bindings_mapped family binding hm
  have hf := Bridge.steps_faithful (initial_faithful family values hv) hs
  have hr := Bridge.steps_reached .empty hs
  have hn : Ptx.Async.complete state.protocol binding.ticket ≠ true := by
    intro hcomplete
    exact hp (completed_use_done hr (by simpa only [hwork] using hf _ _ hmap.2 hcomplete) hu)
  have hb := Regions.borrowed_steps (bindings_borrowed family values hv) hs
  have hh := hb binding hm hn
  have heq : binding.buffer = target := by
    by_contra hne
    exact regions_separated tiles _ _ _ _ hmap.1 hl hne loc hregion hcontains
  subst target
  exact ⟨Ptx.Async.reclaim_of_holds hh,fun value => Ptx.Async.hostWrite_of_holds hh⟩

end
end Ptx.Kernels.HopperDoubleBuffer.Whole
