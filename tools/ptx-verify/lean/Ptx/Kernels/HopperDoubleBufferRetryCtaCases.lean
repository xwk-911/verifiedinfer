import Ptx.Kernels.HopperDoubleBufferRetryNativeCases
import Ptx.Kernels.HopperDoubleBufferControlCtaTrace

/-! Actual CTA generations and local source cases with arbitrary failed waits.
Retry/prefetch/native work preserves CTA counters. Only actual CTA steps
advance them; no matching-participant or control-rank premise is assumed. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def ReplySourceFamily.reuseCtaId {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (lane : Wgmma.Lane) (arrival : Bool) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+
    family.schedules lane tile+preludeEventCount tile tiles (HopperStage.leader lane)+5+ctaOffset arrival⟩
def ReplySourceFamily.returnCtaId {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (lane : Wgmma.Lane) (arrival : Bool) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles+4+ctaOffset arrival⟩
inductive RetryCtaSource {tiles candidate} (family : ReplySourceFamily tiles candidate) : Ptx.Event.EventId → Bool → (Nat × Nat) → Prop
  | initial (lane : Wgmma.Lane) (arrival : Bool) : RetryCtaSource family (initialCtaId tiles lane arrival) arrival (0,0)
  | reuse (tile : Nat) (lane : Wgmma.Lane) (arrival : Bool) (ht : tile < tiles) :
      RetryCtaSource family (family.reuseCtaId tile lane arrival) arrival (2,tile)
  | output (lane : Wgmma.Lane) (arrival : Bool) : RetryCtaSource family (family.returnCtaId lane arrival) arrival (1,0)

theorem reply_checkpoint_generations (tiles lane reply retries n) :
    generations (replyTileCheckpoint tiles lane reply retries n).1 = loopGenerations n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : generations (replyTileCheckpoint tiles lane reply retries (n+1)).1 =
        (2,Ptx.Event.generation (replyTileCheckpoint tiles lane reply retries n).1.base.scalar.core 2+1)::
          (generations (replyTileCheckpoint tiles lane reply retries n).1).filter (fun kv => kv.1 != 2) := by
      simp only [replyTileCheckpoint,loopCheckpoint,Nat.zero_add,iteration_generations]
    rw [he]
    change (2,(((generations (replyTileCheckpoint tiles lane reply retries n).1).find? (fun kv => kv.1 == 2)).map Prod.snd).getD 0+1)::
      (generations (replyTileCheckpoint tiles lane reply retries n).1).filter (fun kv => kv.1 != 2) = _
    rw [ih]
    cases n <;> simp [loopGenerations]

theorem reply_prepared_generation_two (tiles lane reply retries tile) :
    Ptx.Event.generation (computeState (ctx tiles lane) reply
      (preparedState (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile) (HopperStage.leader lane))
      (aDescriptor (stage tile)) (bDescriptor (stage tile)) (replyTileCheckpoint tiles lane reply retries tile).2).base.scalar.core 2 = tile := by
  simp only [Ptx.Event.generation,compute_generations,prepared_generations,reply_checkpoint_generations]
  cases tile <;> simp [loopGenerations]

theorem reply_return_generation_one (tiles lane reply retries) :
    Ptx.Event.generation (outputStored (outputAddressState (replyCheckpoint tiles lane reply retries).1 lane)).base.scalar.core 1 = 0 := by
  have hg : generations (replyCheckpoint tiles lane reply retries).1 = loopGenerations tiles := reply_checkpoint_generations tiles lane reply retries tiles
  simp only [Ptx.Event.generation,output_generations,hg]
  cases tiles <;> simp [loopGenerations]

theorem cta_tag_absent_of_empty_filter {events : List Wgmma.Event} {index : Nat} {event : Wgmma.Event} {arrival : Bool} {tag : Nat × Nat}
    (hn : events.filterMap (sourceCtaTag arrival) = []) (he : events[index]? = some event) (hs : sourceCtaTag arrival event = some tag) : False := by
  have hm := List.mem_filterMap.mpr ⟨event,List.mem_of_getElem? he,hs⟩
  rw [hn] at hm
  cases hm

theorem wait_replicate_cta_tags_empty (context bar parity retries answer arrival) :
    (List.replicate retries (waitEvent context bar parity answer)).filterMap (sourceCtaTag arrival) = [] := by
  induction retries with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.filterMap_cons,waitEvent,sourceCtaTag,Unified.eventView] using ih
theorem prelude_cta_tags_empty (context reply s tile tiles leader mapA mapB arrival) :
    (preludeEvents context reply s tile tiles leader mapA mapB).filterMap (sourceCtaTag arrival) = [] := by
  unfold preludeEvents
  split_ifs <;> rfl

theorem retry_initial_cta_case {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane)
    (index : Nat) (event : Wgmma.Event) (arrival : Bool) (tag : Nat × Nat)
    (he : (replyInitialEvents lane (family.replies lane))[index]? = some event) (htag : sourceCtaTag arrival event = some tag) :
    RetryCtaSource family ⟨(ctx tiles lane).id,index⟩ arrival tag := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  rw [reply_initial_events_length] at hi
  cases hl : HopperStage.leader lane
  · have hb : index < 2 := by simpa only [hl,Bool.false_eq_true,ite_false] using hi
    interval_cases index
    all_goals simp only [replyInitialEvents,hl,initializationEvents,replyInitialCopies,Bool.false_eq_true,ite_false,
      List.nil_append,List.append_nil,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    all_goals cases he
    all_goals cases arrival <;> simp only [sourceCtaTag,Unified.eventView,Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,reduceCtorEq] at htag
    all_goals cases htag
    all_goals first
      | simpa only [initialCtaId,hl,ctaOffset,ite_true,ite_false,Bool.false_eq_true] using RetryCtaSource.initial (family := family) lane false
      | simpa only [initialCtaId,hl,ctaOffset,ite_true,ite_false,Bool.false_eq_true] using RetryCtaSource.initial (family := family) lane true
  · have hz : lane = 0 := (leader_iff_zero lane).mp hl
    subst lane
    have hb : index < 8 := hi
    interval_cases index
    all_goals cases he
    all_goals cases arrival <;> simp only [sourceCtaTag,Unified.eventView,Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,reduceCtorEq] at htag
    all_goals cases htag
    all_goals first | exact RetryCtaSource.initial 0 false | exact RetryCtaSource.initial 0 true

theorem retry_iteration_cta_case {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) (ht : tile < tiles)
    (index : Nat) (event : Wgmma.Event) (arrival : Bool) (tag : Nat × Nat)
    (he : (replyIterationEvents tiles lane (family.replies lane) (family.schedules lane) tile)[index]? = some event)
    (htag : sourceCtaTag arrival event = some tag) :
    RetryCtaSource family ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+index⟩ arrival tag := by
  dsimp only [replyIterationEvents,iterationEvents] at he
  rw [List.append_assoc] at he
  by_cases hh : index < family.schedules lane tile+1
  · rw [List.getElem?_append_left (by simpa only [List.length_append,List.length_replicate,List.length_cons,List.length_nil] using hh)] at he
    exact (cta_tag_absent_of_empty_filter (by rw [List.filterMap_append,wait_replicate_cta_tags_empty]; rfl) he htag).elim
  · rw [List.getElem?_append_right (by simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil]; omega)] at he
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil] at he
    by_cases hp : index-(family.schedules lane tile+1) < preludeEventCount tile tiles (HopperStage.leader lane)
    · rw [List.getElem?_append_left (by rwa [prelude_events_length])] at he
      exact (cta_tag_absent_of_empty_filter (prelude_cta_tags_empty _ _ _ _ _ _ _ _ _) he htag).elim
    · rw [List.getElem?_append_right (by rw [prelude_events_length]; omega),prelude_events_length] at he
      by_cases hc : index-(family.schedules lane tile+1)-preludeEventCount tile tiles (HopperStage.leader lane) < 4
      · rw [List.getElem?_append_left (by change index-(family.schedules lane tile+1)-preludeEventCount tile tiles (HopperStage.leader lane) < 4; exact hc)] at he
        exact (cta_tag_absent_of_empty_filter (by rfl) he htag).elim
      · rw [List.getElem?_append_right (by change 4 ≤ index-(family.schedules lane tile+1)-preludeEventCount tile tiles (HopperStage.leader lane); omega)] at he
        simp only [computeEvents,List.length_cons,List.length_nil,Nat.zero_add] at he
        have hi : index-(family.schedules lane tile+1)-preludeEventCount tile tiles (HopperStage.leader lane)-4 < 2 :=
          (List.getElem?_eq_some_iff.mp he).1
        have hj : index-(family.schedules lane tile+1)-preludeEventCount tile tiles (HopperStage.leader lane)-4 = 0 ∨
            index-(family.schedules lane tile+1)-preludeEventCount tile tiles (HopperStage.leader lane)-4 = 1 := by omega
        rcases hj with hj | hj
        all_goals rw [hj] at he
        all_goals simp only [advanceEvents,List.getElem?_cons_zero,List.getElem?_cons_succ] at he
        all_goals cases he
        all_goals cases arrival <;> simp only [sourceCtaTag,Unified.eventView,reply_prepared_generation_two,
          Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,reduceCtorEq] at htag
        all_goals cases htag
        all_goals first
          | (have hid : (⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+index⟩ : Ptx.Event.EventId) =
                family.reuseCtaId tile lane true := by
               apply congrArg₂ Ptx.Event.EventId.mk rfl
               dsimp [ReplySourceFamily.reuseCtaId,ctaOffset]
               omega
             rw [hid]
             exact RetryCtaSource.reuse tile lane true ht)
          | (have hid : (⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+index⟩ : Ptx.Event.EventId) =
                family.reuseCtaId tile lane false := by
               apply congrArg₂ Ptx.Event.EventId.mk rfl
               dsimp [ReplySourceFamily.reuseCtaId,ctaOffset]
               omega
             rw [hid]
             exact RetryCtaSource.reuse tile lane false ht)

theorem retry_output_cta_case {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane)
    (index : Nat) (event : Wgmma.Event) (arrival : Bool) (tag : Nat × Nat)
    (he : (outputEvents (ctx tiles lane) (replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).1 lane (HopperStage.leader lane)
      (replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).2)[index]? = some event)
    (htag : sourceCtaTag arrival event = some tag) :
    RetryCtaSource family ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles+index⟩ arrival tag := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  cases hl : HopperStage.leader lane
  · have hb : index < 6 := by simpa only [outputEvents,returnEvents,hl,Bool.false_eq_true,ite_false,
        List.length_append,outputWriteEvents,List.length_cons,List.length_nil] using hi
    interval_cases index
    all_goals simp only [outputEvents,returnEvents,hl,Bool.false_eq_true,ite_false,outputWriteEvents,reply_return_generation_one,
      List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    all_goals cases he
    all_goals cases arrival <;> simp only [sourceCtaTag,Unified.eventView,Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,reduceCtorEq] at htag
    all_goals cases htag
    all_goals first
      | simpa only [ReplySourceFamily.returnCtaId,ctaOffset,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using RetryCtaSource.output (family := family) lane false
      | simpa only [ReplySourceFamily.returnCtaId,ctaOffset,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using RetryCtaSource.output (family := family) lane true
  · have hz : lane = 0 := (leader_iff_zero lane).mp hl
    subst lane
    have hb : index < 8 := by simpa only [outputEvents,returnEvents,hl,ite_true,
        List.length_append,outputWriteEvents,List.length_cons,List.length_nil] using hi
    interval_cases index
    all_goals simp only [outputEvents,returnEvents,hl,ite_true,outputWriteEvents,reply_return_generation_one,
      List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    all_goals cases he
    all_goals cases arrival <;> simp only [sourceCtaTag,Unified.eventView,Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,reduceCtorEq] at htag
    all_goals cases htag
    all_goals first
      | simpa only [ReplySourceFamily.returnCtaId,ctaOffset,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using RetryCtaSource.output (family := family) 0 false
      | simpa only [ReplySourceFamily.returnCtaId,ctaOffset,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using RetryCtaSource.output (family := family) 0 true

end
end Ptx.Kernels.HopperDoubleBuffer
