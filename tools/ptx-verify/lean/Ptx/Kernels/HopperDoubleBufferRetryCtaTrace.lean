import Ptx.Kernels.HopperDoubleBufferRetryCtaCases

/-! Exhaustive actual CTA identities for arbitrary-retry rich traces, with
the converse expected-event witnesses. Tags retain actual generations and
source serials; source coverage is derived from the checked candidate. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_loop_cta_case {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) (n : Nat) (hn : n ≤ tiles)
    (index : Nat) (event : Wgmma.Event) (arrival : Bool) (tag : Nat × Nat)
    (he : (replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) n)[index]? = some event)
    (htag : sourceCtaTag arrival event = some tag) :
    RetryCtaSource family ⟨(ctx tiles lane).id,(replyInitialEvents lane (family.replies lane)).length+index⟩ arrival tag := by
  induction n generalizing index with
  | zero => simp [replyLoopEvents,loopEvents] at he
  | succ n ih =>
    have hs : replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) (n+1) =
        replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) n++
          replyIterationEvents tiles lane (family.replies lane) (family.schedules lane) n := by
      simp only [replyLoopEvents,loopEvents,replyIterationEvents,replyTileCheckpoint,Nat.zero_add]
    by_cases hi : index < (replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) n).length
    · rw [hs,List.getElem?_append_left hi] at he
      exact ih (by omega) index he
    · rw [hs,List.getElem?_append_right (by omega)] at he
      have hc := retry_iteration_cta_case family n lane (by omega) _ event arrival tag he htag
      have hindex : replyTileStart tiles lane (family.replies lane) (family.schedules lane) n+
          (index-(replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) n).length) =
          (replyInitialEvents lane (family.replies lane)).length+index := by unfold replyTileStart; omega
      simpa only [hindex] using hc

theorem retry_complete_cta_case {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane)
    (index : Nat) (event : Wgmma.Event) (arrival : Bool) (tag : Nat × Nat)
    (he : (replyPositiveEvents tiles lane (family.replies lane) (family.schedules lane))[index]? = some event)
    (htag : sourceCtaTag arrival event = some tag) : RetryCtaSource family ⟨(ctx tiles lane).id,index⟩ arrival tag := by
  simp only [replyPositiveEvents,← List.append_assoc] at he
  change ((replyInitialEvents lane (family.replies lane)++replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) tiles)++_)[index]? = some event at he
  by_cases hi : index < replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles
  · rw [List.getElem?_append_left (by simpa only [List.length_append,replyTileStart] using hi)] at he
    by_cases hinitial : index < (replyInitialEvents lane (family.replies lane)).length
    · rw [List.getElem?_append_left hinitial] at he
      exact retry_initial_cta_case family lane index event arrival tag he htag
    · rw [List.getElem?_append_right (by omega)] at he
      have hc := retry_loop_cta_case family lane tiles (Nat.le_refl _) _ event arrival tag he htag
      simpa only [show (replyInitialEvents lane (family.replies lane)).length+
        (index-(replyInitialEvents lane (family.replies lane)).length) = index by omega] using hc
  · rw [List.getElem?_append_right (by simpa only [List.length_append,replyTileStart] using Nat.le_of_not_gt hi)] at he
    have hc := retry_output_cta_case family lane _ event arrival tag he htag
    have hindex : replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles+
        (index-(replyInitialEvents lane (family.replies lane)++replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) tiles).length) = index := by
      simp only [List.length_append,replyTileStart]
      unfold replyTileStart at hi
      omega
    simpa only [hindex] using hc

theorem retry_candidate_cta_case {tiles initial candidate id event arrival tag} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (he : candidate.eventAt id = some event)
    (htag : sourceCtaTag arrival event = some tag) : RetryCtaSource family id arrival tag := by
  obtain ⟨trace,ht,hid,hget⟩ := Unified.eventAt_trace he
  obtain ⟨lane,rfl⟩ := retry_trace_family family hw ht
  rw [family.events] at hget
  have hc := retry_complete_cta_case family lane id.serial event arrival tag hget htag
  have hthread : (ctx tiles lane).id = id.thread := (family.ids lane).symm.trans hid
  have hsame : (⟨(ctx tiles lane).id,id.serial⟩ : Ptx.Event.EventId) = id := by cases id; exact congrArg₂ Ptx.Event.EventId.mk hthread rfl
  rw [hsame] at hc
  exact hc

theorem retry_view_cta_case {tiles initial candidate id arrival tag} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (he : candidate.view.ctaTag arrival id = some tag) :
    RetryCtaSource family id arrival tag := by
  obtain ⟨event,hget,htag⟩ := view_cta_source_tag he
  exact retry_candidate_cta_case family hw hget htag

theorem view_cta_tag_of_source {candidate : Unified.Candidate} {id event arrival tag}
    (he : candidate.eventAt id = some event) (htag : sourceCtaTag arrival event = some tag) :
    candidate.view.ctaTag arrival id = some tag := by
  unfold Hopper.Candidate.ctaTag
  rw [Unified.view_eventAt,he]
  exact htag

theorem reply_complete_output_at (tiles lane reply retries index event)
    (he : (outputEvents (ctx tiles lane) (replyCheckpoint tiles lane reply retries).1 lane (HopperStage.leader lane)
      (replyCheckpoint tiles lane reply retries).2)[index]? = some event) :
    (replyPositiveEvents tiles lane reply retries)[replyTileStart tiles lane reply retries tiles+index]? = some event := by
  simp only [replyPositiveEvents,← List.append_assoc]
  change ((replyInitialEvents lane reply++replyLoopEvents tiles lane reply retries tiles)++_)[_]? = _
  rw [List.getElem?_append_right (by simp only [List.length_append]; unfold replyTileStart; omega)]
  rw [show replyTileStart tiles lane reply retries tiles+index-
      (replyInitialEvents lane reply++replyLoopEvents tiles lane reply retries tiles).length = index by
    simp only [List.length_append,replyTileStart]; omega]
  exact he

theorem retry_initial_cta_tag {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (lane : Wgmma.Lane) (arrival : Bool) :
    candidate.view.ctaTag arrival (initialCtaId tiles lane arrival) = some (0,0) := by
  have hb : ((replyInitialEvents lane (family.replies lane))[(initialCtaId tiles lane arrival).serial]?).bind (sourceCtaTag arrival) = some (0,0) := by
    cases hl : HopperStage.leader lane <;> cases arrival <;>
      simp [initialCtaId,replyInitialEvents,initializationEvents,replyInitialCopies,ctaOffset,hl,sourceCtaTag,Unified.eventView]
  obtain ⟨event,he,htag⟩ := Option.bind_eq_some_iff.mp hb
  exact view_cta_tag_of_source (family_event_at family hw lane _ _ (reply_complete_initial_at tiles lane (family.replies lane) (family.schedules lane) _ event he)) htag

theorem retry_iteration_cta_tag_at {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) (arrival : Bool) :
    ((replyIterationEvents tiles lane (family.replies lane) (family.schedules lane) tile)[family.schedules lane tile+
      preludeEventCount tile tiles (HopperStage.leader lane)+5+ctaOffset arrival]?).bind (sourceCtaTag arrival) = some (2,tile) := by
  simp only [replyIterationEvents,iterationEvents,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
  simp only [List.length_replicate]
  rw [List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by rw [prelude_events_length]; omega),prelude_events_length]
  rw [List.getElem?_append_right (by change 4 ≤ _; omega)]
  simp only [computeEvents,List.length_cons,List.length_nil]
  rw [show family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+5+ctaOffset arrival-
      family.schedules lane tile-1-preludeEventCount tile tiles (HopperStage.leader lane)-4 = ctaOffset arrival by omega]
  cases arrival <;> simp [advanceEvents,ctaOffset,sourceCtaTag,Unified.eventView,reply_prepared_generation_two]

theorem retry_reuse_cta_tag {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) (arrival : Bool) :
    candidate.view.ctaTag arrival (family.reuseCtaId tile lane arrival) = some (2,tile) := by
  obtain ⟨event,he,htag⟩ := Option.bind_eq_some_iff.mp (retry_iteration_cta_tag_at family tile lane arrival)
  have hc := family_event_at family hw lane _ _ (reply_complete_iteration_at tiles lane (family.replies lane) (family.schedules lane) tile _ event ht he)
  have hactual : candidate.eventAt (family.reuseCtaId tile lane arrival) = some event := by
    simpa only [ReplySourceFamily.reuseCtaId,Nat.add_assoc] using hc
  exact view_cta_tag_of_source hactual htag

theorem retry_return_cta_tag {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (lane : Wgmma.Lane) (arrival : Bool) :
    candidate.view.ctaTag arrival (family.returnCtaId lane arrival) = some (1,0) := by
  have hb : ((outputEvents (ctx tiles lane) (replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).1 lane (HopperStage.leader lane)
      (replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).2)[4+ctaOffset arrival]?).bind (sourceCtaTag arrival) = some (1,0) := by
    cases arrival <;> simp [outputEvents,outputWriteEvents,returnEvents,ctaOffset,sourceCtaTag,Unified.eventView,reply_return_generation_one]
  obtain ⟨event,he,htag⟩ := Option.bind_eq_some_iff.mp hb
  have hc := family_event_at family hw lane _ _ (reply_complete_output_at tiles lane (family.replies lane) (family.schedules lane) _ event he)
  have hactual : candidate.eventAt (family.returnCtaId lane arrival) = some event := by
    simpa only [ReplySourceFamily.returnCtaId,Nat.add_assoc] using hc
  exact view_cta_tag_of_source hactual htag

end
end Ptx.Kernels.HopperDoubleBuffer
