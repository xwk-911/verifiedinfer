import Ptx.Kernels.HopperDoubleBufferRetryArbitraryOutput
import Ptx.Hopper.UnifiedExecution

/-! All actual source-matched collectives correspond to one source tile. Group
and lane identities prevent mixing tiles or lanes. Candidate-wide tensor
admission is equivalent to the earlier per-tile component, not a strengthening
silently introduced by the unified execution entry. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem family_collective_identity {tiles initial candidate issue} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (collective : Unified.Collective candidate issue) :
    ∃ tile, tile < tiles ∧ issue = family.mmaId tile 0 ∧ collective.calls = family.calls tile := by
  have he : candidate.eventAt issue = some (.mma (collective.marks 0) (collective.calls 0)) := by
    simpa only [collective.representative] using collective.matched 0
  obtain ⟨tile,lane,ht,hid,_,hcall⟩ := retry_native_mma_case family hw he
  have hlane := congrArg Wgmma.Call.lane hcall
  have hflane : (family.calls tile lane).lane = lane := (familyCollective family hw tile ht).cohort.lane lane
  rw [collective.cohort.lane,hflane] at hlane
  subst lane
  rw [retry_native_mma_id] at hid
  refine ⟨tile,ht,hid,?_⟩
  funext member
  obtain ⟨other,actual,ho,_,_,hc⟩ := retry_native_mma_case family hw (collective.matched member)
  have hg := congrArg Wgmma.Call.group hc
  rw [collective.cohort.group,hcall] at hg
  change (replyCall tiles 0 (family.replies 0) (family.schedules 0) tile).group =
    (replyCall tiles actual (family.replies actual) (family.schedules actual) other).group at hg
  rw [reply_call_group,reply_call_group] at hg
  subst other
  have hl := congrArg Wgmma.Call.lane hc
  have hf : (family.calls tile actual).lane = actual := (familyCollective family hw tile ht).cohort.lane actual
  rw [collective.cohort.lane,hf] at hl
  subst actual
  exact hc

theorem family_collective_sources {tiles initial candidate issue} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (collective : Unified.Collective candidate issue) :
    ∃ tile, tile < tiles ∧ issue = family.mmaId tile 0 ∧ collective.sources = family.mmaId tile := by
  obtain ⟨tile,ht,hissue,hcalls⟩ := family_collective_identity family hw collective
  refine ⟨tile,ht,hissue,?_⟩
  funext lane
  obtain ⟨other,member,ho,hid,_,hc⟩ := retry_native_mma_case family hw (collective.matched lane)
  have hg := congrArg Wgmma.Call.group hc
  rw [hcalls] at hg
  change (replyCall tiles lane (family.replies lane) (family.schedules lane) tile).group =
    (replyCall tiles member (family.replies member) (family.schedules member) other).group at hg
  rw [reply_call_group,reply_call_group] at hg
  subst other
  have hl := congrArg Wgmma.Call.lane hc
  have hfl : (family.calls tile lane).lane = lane := (familyCollective family hw tile ht).cohort.lane lane
  have hfm : (family.calls tile member).lane = member := (familyCollective family hw tile ht).cohort.lane member
  rw [hcalls,hfl,hfm] at hl
  subst member
  exact hid.trans (retry_native_mma_id family tile lane)

theorem family_tensor_components_iff {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) :
    Unified.TensorComponents candidate ↔ ∀ tile, tile < tiles → ∃ memory, Wgmma.TensorConditions .zero (family.calls tile) memory := by
  constructor
  · intro htensor tile ht
    exact htensor.tensor _ (familyCollective family hw tile ht)
  · intro htensor
    constructor
    · intro event mark call he
      obtain ⟨tile,lane,ht,hid,_,_⟩ := retry_native_mma_case family hw he
      exact ⟨family.mmaId tile 0,familyCollective family hw tile ht,lane,
        (hid.trans (retry_native_mma_id family tile lane)).symm⟩
    · intro issue collective
      obtain ⟨tile,ht,hissue,hcalls⟩ := family_collective_identity family hw collective
      have hcta : issue.thread.cta = .zero := by rw [hissue]; rfl
      rw [hcta,hcalls]
      exact htensor tile ht

end
end Ptx.Kernels.HopperDoubleBuffer
