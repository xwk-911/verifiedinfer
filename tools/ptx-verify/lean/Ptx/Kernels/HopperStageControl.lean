import Ptx.Kernels.HopperStageControlData

/-! A rank witness for source PO, both CTA rendezvous, actual TMA internal
nodes and exhaustive mbarrier serialization. This is a control consistency
proof; none of these ranks grants shared-memory visibility or protects reuse.
-/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

theorem source_rank_strict {thread : ThreadId} {left right : Nat}
    (hl : thread.tid.linear block < 128) (hs : left < right) :
    sourceControlRank ⟨thread,left⟩ < sourceControlRank ⟨thread,right⟩ := by
  dsimp only [sourceControlRank]
  split_ifs <;> omega
theorem control_program_order {left right} (hp : Tma.ProgramOrder resourceCandidate left right) :
    controlRank left < controlRank right := by
  cases left <;> cases right <;> try exact False.elim hp
  rename_i left right
  obtain ⟨lane,hid,_⟩ := resource_present_has_lane hp.1
  have hl : left.thread.tid.linear block < 128 := by
    rw [hid]
    change Ampere.linearThread (ctx lane) < 128
    rw [ctx_linear]
    exact lane.isLt
  rcases left with ⟨thread,serial⟩
  rcases right with ⟨other,last⟩
  have he : thread = other := hp.2.2.1
  subst other
  exact source_rank_strict hl hp.2.2.2
theorem control_cta_order {left right} (hc : Tma.CTAControl resourceCandidate left right) :
    controlRank left < controlRank right := by
  cases left <;> cases right <;> try exact False.elim hc
  rename_i left right
  change Hopper.CTAControl resourceCandidate left right at hc
  cases ha : resourceCandidate.ctaTag true left with
  | none => simp [Hopper.CTAControl,ha] at hc
  | some a =>
    cases hb : resourceCandidate.ctaTag false right with
    | none => simp [Hopper.CTAControl,hb] at hc
    | some b =>
      have he : a = b := (show left.thread.cta = right.thread.cta ∧ a = b by simpa only [Hopper.CTAControl,ha,hb] using hc).2
      subst b
      have hr := cta_tag_rank left (Hopper.present_mem_eventIds (Hopper.cta_tag_present ha)) true a (by simp only [ha,Option.toList_some,List.mem_singleton])
      have hs := cta_tag_rank right (Hopper.present_mem_eventIds (Hopper.cta_tag_present hb)) false a (by simp only [hb,Option.toList_some,List.mem_singleton])
      change sourceControlRank left < sourceControlRank right
      simp at hr hs
      rw [hr,hs]
      split_ifs <;> omega

end
end Ptx.Kernels.HopperStage
