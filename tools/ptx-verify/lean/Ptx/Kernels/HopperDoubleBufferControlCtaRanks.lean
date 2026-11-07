import Ptx.Kernels.HopperDoubleBufferControlCtaTrace
import Ptx.Kernels.HopperDoubleBufferControlResources

/-! The actual CTA arrivals and returns occupy consecutive global clock
intervals for the same barrier/generation, across all 128 lanes. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def ctaBaseTick (tiles : Nat) (tag : Nat × Nat) : Nat :=
  if tag.1 = 0 then 3 else if tag.1 = 2 then 16+10*tag.2 else 12+10*tiles
def ctaTick (tiles : Nat) (tag : Nat × Nat) (arrival : Bool) : Nat := ctaBaseTick tiles tag+ctaOffset arrival

theorem cta_offset_bounded (arrival : Bool) : ctaOffset arrival ≤ 1 := by cases arrival <;> decide

theorem producer_reuse_tick (tiles tile offset) (ht : tile < tiles) (ho : offset ≤ 1) :
    producerTick tiles (8+10*tile+(if tile+1 < tiles then 3 else 0)+5+offset) = 16+10*tile+offset := by
  have hz : tiles ≠ 0 := by omega
  by_cases hn : tile+1 < tiles
  · rw [ite_eq_left hn,producer_tick_before tiles _ (by simp only [producerThreshold,hz,ite_false]; omega)]
    omega
  · rw [ite_eq_right hn,producer_tick_after tiles _ (by simp only [producerThreshold,hz,ite_false]; omega)]
    omega

theorem data_peer_pre_output_length (a b tiles lane) (hl : HopperStage.leader lane = false) :
    (dataPreOutputEvents a b tiles lane).length = 2+7*tiles := by
  by_cases hz : tiles = 0
  · subst tiles
    simp [dataPreOutputEvents,initializationEvents,hl]
  · simp [dataPreOutputEvents,hz,dataKernelLoopEvents,initializationEvents,dataInitialCopies,data_loop_full_length,hl,Nat.add_comm]
    omega

theorem initial_cta_control_rank (tiles lane arrival) :
    sourceControlRank tiles (initialCtaId tiles lane arrival) = 1024*(3+ctaOffset arrival)+lane.val := by
  change 1024*sourceTick tiles (resourceLane (ctx tiles lane).id)
    ((if HopperStage.leader lane then 3 else 0)+ctaOffset arrival)+resourceLane (ctx tiles lane).id = _
  rw [resource_lane_value]
  have hoff := cta_offset_bounded arrival
  by_cases hz : lane.val = 0
  · simp only [sourceTick,HopperStage.leader,decide_eq_true_eq,hz,ite_true]
    rw [producer_initial_tick tiles _ (by omega)]
  · simp only [sourceTick,HopperStage.leader,decide_eq_true_eq,hz,ite_false,Nat.zero_add,peerTick]
    split_ifs <;> omega

theorem reuse_cta_control_rank (a b tiles tile lane arrival) (ht : tile < tiles) :
    sourceControlRank tiles (reuseCtaId a b tiles tile lane arrival) = 1024*(16+10*tile+ctaOffset arrival)+lane.val := by
  change 1024*sourceTick tiles (resourceLane (ctx tiles lane).id)
    (dataTileStart a b tiles tile lane+dataPreludeLength tiles tile lane+5+ctaOffset arrival)+resourceLane (ctx tiles lane).id = _
  rw [resource_lane_value,data_tile_start_value a b tiles tile lane ht]
  have hoff := cta_offset_bounded arrival
  cases hl : HopperStage.leader lane
  · have hz : lane.val ≠ 0 := by intro hz; simp [HopperStage.leader,hz] at hl
    have hp : dataPreludeLength tiles tile lane = 0 := by simp [dataPreludeLength,needsPrefetch,hl]
    simp only [hl,Bool.false_eq_true,ite_false,sourceTick,hz,hp,Nat.add_zero]
    have hs : 2+7*tile+5+ctaOffset arrival = 2+7*tile+(5+ctaOffset arrival) := by omega
    rw [hs,peer_native_tick tiles tile _ ht (by omega)]
    omega
  · have hz : lane.val = 0 := by have he := (leader_iff_zero lane).mp hl; simpa only [he,Fin.val_zero]
    simp only [hl,ite_true,sourceTick,hz,dataPreludeLength,needsPrefetch,hl,and_true]
    rw [producer_reuse_tick tiles tile _ ht hoff]

theorem return_cta_control_rank (a b tiles lane arrival) :
    sourceControlRank tiles (returnCtaId a b tiles lane arrival) = 1024*(12+10*tiles+ctaOffset arrival)+lane.val := by
  change 1024*sourceTick tiles (resourceLane (ctx tiles lane).id)
    ((dataPreOutputEvents a b tiles lane).length+4+ctaOffset arrival)+resourceLane (ctx tiles lane).id = _
  rw [resource_lane_value]
  cases hl : HopperStage.leader lane
  · have hz : lane.val ≠ 0 := by intro hz; simp [HopperStage.leader,hz] at hl
    rw [data_peer_pre_output_length a b tiles lane hl]
    simp only [sourceTick,hz,ite_false]
    have hs : 2+7*tiles+4+ctaOffset arrival = 2+7*tiles+(4+ctaOffset arrival) := by omega
    rw [hs,peer_tail_tick]
    omega
  · have hz : lane = 0 := (leader_iff_zero lane).mp hl
    subst lane
    rw [data_producer_pre_output_length]
    change 1024*producerTick tiles (10*tiles+5+4+ctaOffset arrival)+0 = _
    have hs : 10*tiles+5+4+ctaOffset arrival = 10*tiles+5+(4+ctaOffset arrival) := by omega
    rw [hs,producer_tail_tick]
    omega

theorem data_cta_case_rank (a b tiles id arrival tag) (hc : CtaSource a b tiles id arrival tag) :
    ∃ lane : Wgmma.Lane, sourceControlRank tiles id = 1024*ctaTick tiles tag arrival+lane.val := by
  cases hc with
  | initial lane arrival => exact ⟨lane,initial_cta_control_rank tiles lane arrival⟩
  | reuse tile lane arrival ht => exact ⟨lane,reuse_cta_control_rank a b tiles tile lane arrival ht⟩
  | output lane arrival => exact ⟨lane,return_cta_control_rank a b tiles lane arrival⟩

theorem data_cta_tag_rank (a b tiles id arrival tag)
    (he : (dataCompleteCandidate a b tiles).view.ctaTag arrival id = some tag) :
    ∃ lane : Wgmma.Lane, sourceControlRank tiles id = 1024*ctaTick tiles tag arrival+lane.val :=
  data_cta_case_rank a b tiles id arrival tag (data_view_cta_case a b tiles id arrival tag he)

theorem control_cta_order (a b tiles) {left right} (hc : Tma.CTAControl (dataCompleteCandidate a b tiles).view left right) :
    controlRank tiles left < controlRank tiles right := by
  cases left <;> cases right <;> try exact False.elim hc
  rename_i left right
  change Hopper.CTAControl (dataCompleteCandidate a b tiles).view left right at hc
  cases ha : (dataCompleteCandidate a b tiles).view.ctaTag true left with
  | none => simp [Hopper.CTAControl,ha] at hc
  | some aTag =>
    cases hb : (dataCompleteCandidate a b tiles).view.ctaTag false right with
    | none => simp [Hopper.CTAControl,hb] at hc
    | some bTag =>
      have he : aTag = bTag := (show left.thread.cta = right.thread.cta ∧ aTag = bTag by simpa only [Hopper.CTAControl,ha,hb] using hc).2
      subst bTag
      obtain ⟨first,hfirst⟩ := data_cta_tag_rank a b tiles left true aTag ha
      obtain ⟨last,hlast⟩ := data_cta_tag_rank a b tiles right false aTag hb
      change sourceControlRank tiles left < sourceControlRank tiles right
      rw [hfirst,hlast]
      have hf := first.isLt
      have hl := last.isLt
      simp only [ctaTick,ctaOffset,ite_true,Bool.false_eq_true,ite_false]
      omega

end
end Ptx.Kernels.HopperDoubleBuffer
