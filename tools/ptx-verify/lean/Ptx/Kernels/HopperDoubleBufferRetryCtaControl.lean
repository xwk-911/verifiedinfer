import Ptx.Kernels.HopperDoubleBufferRetryCtaTrace
import Ptx.Kernels.HopperDoubleBufferRetryResourceControl
import Ptx.Kernels.HopperDoubleBufferControlCtaRanks

/-! Actual CTA arrival/return ranks and TMA/resource/CTA control acyclicity
for arbitrary finite retry source families. Unified native control and full
memory/tensor/execution admission remain separate obligations. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_iteration_compute_clock {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (lane : Wgmma.Lane) (index : Fin 6) :
    (retryIterationClocks family tile lane)[family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+index.val]? =
      some (retryClock family (12+10*tile+index.val) lane) := by
  simp only [retryIterationClocks,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [retryFailedClocks,List.length_ofFn]; omega)]
  simp only [retryFailedClocks,List.length_ofFn]
  rw [List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by simp only [retryPreludeClocks,List.length_ofFn]; omega)]
  simp only [retryPreludeClocks,List.length_ofFn]
  rw [show family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+index.val-family.schedules lane tile-1-
    preludeEventCount tile tiles (HopperStage.leader lane) = index.val by omega]
  rw [List.getElem?_eq_getElem (by simpa only [retryComputeClocks,List.length_ofFn] using index.isLt)]
  simp only [retryComputeClocks,List.getElem_ofFn]

theorem retry_compute_source_rank {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) (index : Fin 6) :
    retrySourceRank family ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+
      (family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+index.val)⟩ =
        retryClock family (12+10*tile+index.val) lane := by
  have he := retry_source_iteration_clock family lane tile _ _ ht (retry_iteration_compute_clock family tile lane index)
  have hl : retryRankLane ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+
      (family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+index.val)⟩ = lane :=
    retry_rank_lane_of_thread (tiles := tiles) rfl
  unfold retrySourceRank
  rw [hl]
  change ((retrySourceClocks family lane)[replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+
    (family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+index.val)]?).getD 0 = _
  rw [he]
  rfl

theorem retry_initial_cta_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) (arrival : Bool) :
    retrySourceRank family (initialCtaId tiles lane arrival) = retryClock family (3+ctaOffset arrival) lane := by
  have hoff := cta_offset_bounded arrival
  have bound (leader : Bool) (off : Nat) (ho : off ≤ 1) : (if leader then 3 else 0)+off < if leader then 8 else 2 := by
    cases leader <;> simp_all <;> omega
  have he := retry_initial_source_rank family lane ⟨(if HopperStage.leader lane then 3 else 0)+ctaOffset arrival,
    bound (HopperStage.leader lane) (ctaOffset arrival) hoff⟩
  change retrySourceRank family (initialCtaId tiles lane arrival) = _ at he
  rw [he]
  apply congrArg (fun tick => retryClock family tick lane)
  have aux (leader : Bool) (off : Nat) : (if leader then 3 else 0)+off+(if leader then 0 else 3) = 3+off := by
    cases leader <;> simp <;> omega
  exact aux (HopperStage.leader lane) (ctaOffset arrival)

theorem retry_reuse_cta_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles)
    (lane : Wgmma.Lane) (arrival : Bool) :
    retrySourceRank family (family.reuseCtaId tile lane arrival) = retryClock family (16+10*tile+ctaOffset arrival) lane := by
  have hoff := cta_offset_bounded arrival
  have he := retry_compute_source_rank family tile ht lane ⟨4+ctaOffset arrival,by omega⟩
  have hid : (⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+
      (family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+(4+ctaOffset arrival))⟩ : Ptx.Event.EventId) =
      family.reuseCtaId tile lane arrival := by
    apply congrArg₂ Ptx.Event.EventId.mk rfl
    omega
  change retrySourceRank family ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+
    (family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+1+(4+ctaOffset arrival))⟩ = _ at he
  rw [hid,show 12+10*tile+(4+ctaOffset arrival) = 16+10*tile+ctaOffset arrival by omega] at he
  exact he

theorem retry_return_cta_rank {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) (arrival : Bool) :
    retrySourceRank family (family.returnCtaId lane arrival) = retryClock family (12+10*tiles+ctaOffset arrival) lane := by
  have hoff := cta_offset_bounded arrival
  have hmin : 6 ≤ if HopperStage.leader lane then 8 else 6 := by split_ifs <;> omega
  have he := retry_output_source_rank family lane ⟨4+ctaOffset arrival,by omega⟩
  have hid : (⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles+(4+ctaOffset arrival)⟩ : Ptx.Event.EventId) =
      family.returnCtaId lane arrival := by
    apply congrArg₂ Ptx.Event.EventId.mk rfl
    omega
  change retrySourceRank family ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles+(4+ctaOffset arrival)⟩ = _ at he
  rw [hid,show 8+10*tiles+(4+ctaOffset arrival) = 12+10*tiles+ctaOffset arrival by omega] at he
  exact he

theorem retry_cta_case_rank {tiles candidate id arrival tag} (family : ReplySourceFamily tiles candidate) (hc : RetryCtaSource family id arrival tag) :
    ∃ lane : Wgmma.Lane, retrySourceRank family id = retryClock family (ctaTick tiles tag arrival) lane := by
  cases hc with
  | initial lane arrival => exact ⟨lane,by simpa [ctaTick,ctaBaseTick] using retry_initial_cta_rank family lane arrival⟩
  | reuse tile lane arrival ht => exact ⟨lane,by simpa [ctaTick,ctaBaseTick] using retry_reuse_cta_rank family tile ht lane arrival⟩
  | output lane arrival => exact ⟨lane,by simpa [ctaTick,ctaBaseTick] using retry_return_cta_rank family lane arrival⟩

theorem retry_cta_tag_rank {tiles initial candidate id arrival tag} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (he : candidate.view.ctaTag arrival id = some tag) :
    ∃ lane : Wgmma.Lane, retrySourceRank family id = retryClock family (ctaTick tiles tag arrival) lane :=
  retry_cta_case_rank family (retry_view_cta_case family hw he)

theorem retry_control_cta_order {tiles initial candidate left right} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Tma.CTAControl candidate.view left right) :
    retryTmaRank family left < retryTmaRank family right := by
  cases left <;> cases right <;> try exact False.elim hc
  rename_i left right
  change Hopper.CTAControl candidate.view left right at hc
  cases ha : candidate.view.ctaTag true left with
  | none => simp [Hopper.CTAControl,ha] at hc
  | some aTag =>
    cases hb : candidate.view.ctaTag false right with
    | none => simp [Hopper.CTAControl,hb] at hc
    | some bTag =>
      have he : aTag = bTag := (show left.thread.cta = right.thread.cta ∧ aTag = bTag by simpa only [Hopper.CTAControl,ha,hb] using hc).2
      subst bTag
      obtain ⟨first,hfirst⟩ := retry_cta_tag_rank family hw ha
      obtain ⟨last,hlast⟩ := retry_cta_tag_rank family hw hb
      change retrySourceRank family left < retrySourceRank family right
      rw [hfirst,hlast]
      apply Nat.mul_lt_mul_of_pos_left _ (retry_unit_pos family)
      have hf := first.isLt
      have hl := last.isLt
      simp only [ctaTick,ctaOffset,ite_true,Bool.false_eq_true,ite_false]
      omega

theorem retry_tma_control_acyclic {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) :
    Tma.ControlAcyclic candidate.view (retryHistories family) :=
  Tma.control_acyclic_of_rank (retryTmaRank family)
    (fun _ _ => retry_tma_program_order family hw)
    (fun _ _ => retry_control_cta_order family hw)
    (fun _ _ => retry_tma_internal_order family ht hw)
    (fun _ _ => retry_control_resource_order family)

theorem retry_tma_components {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hp : Tma.PayloadAgreement candidate.view initial) :
    Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) (retryHistories family) :=
  ⟨hw,hc,hd,hp,retry_all_histories_valid family ht hw hd,retry_tma_control_acyclic family ht hw⟩

theorem completed_positive_tma_control {tiles initial candidate} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate) :
    ∃ family : ReplySourceFamily tiles candidate, Tma.ControlAcyclic candidate.view (retryHistories family) := by
  obtain ⟨family⟩ := completed_candidate_reply_family ht hb hw hc
  exact ⟨family,retry_tma_control_acyclic family ht hw⟩

end
end Ptx.Kernels.HopperDoubleBuffer
