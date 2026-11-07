import Ptx.Kernels.HopperDoubleBufferReplyCollective
import Ptx.Hopper.UnifiedNativeOrder

/-! Reconstruct source collectives and wait-before-MMA order for every
well-formed completed positive launch, with arbitrary lane replies/retries.
No tensor arithmetic, native-control or resource completion is assumed by
collective reconstruction. Publication still needs actual completion histories.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

structure ReplySourceFamily (tiles : Nat) (candidate : Unified.Candidate) where
  replies : Wgmma.Lane → Wgmma.Oracle
  schedules : Wgmma.Lane → Nat → Nat
  traces : Wgmma.Lane → Unified.ThreadTrace
  members : ∀ lane, traces lane ∈ candidate.traces
  ids : ∀ lane, (traces lane).id = (ctx tiles lane).id
  oracles : ∀ lane, (traces lane).oracle = replies lane
  events : ∀ lane, (traces lane).events = replyPositiveEvents tiles lane (replies lane) (schedules lane)

def ReplySourceFamily.waitId {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) : Ptx.Event.EventId :=
  replyWaitId tiles lane (family.replies lane) (family.schedules lane) tile
def ReplySourceFamily.failedWaitId {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) (attempt : Nat) : Ptx.Event.EventId :=
  replyFailedWaitId tiles lane (family.replies lane) (family.schedules lane) tile attempt
def ReplySourceFamily.mmaId {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) : Ptx.Event.EventId :=
  replyMmaId tiles lane (family.replies lane) (family.schedules lane) tile
def ReplySourceFamily.calls {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) : Wgmma.Call :=
  replyCall tiles lane (family.replies lane) (family.schedules lane) tile
def ReplySourceFamily.marks {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane) : Wgmma.Mark :=
  replyMark tiles lane (family.replies lane) (family.schedules lane) tile

theorem completed_candidate_reply_family {tiles initial candidate} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate) :
    Nonempty (ReplySourceFamily tiles candidate) := by
  classical
  have hex : ∀ lane : Wgmma.Lane, ∃ reply retries trace, trace ∈ candidate.traces ∧ trace.id = (ctx tiles lane).id ∧
      trace.oracle = reply ∧ trace.events = replyPositiveEvents tiles lane reply retries := by
    intro lane
    obtain ⟨trace,hm,hid⟩ := hw.2.2.2 (ctx tiles lane).id (HopperStage.ctx_valid lane)
    have hs := (hw.2.2.1 trace hm).2
    change Wgmma.run {id := trace.id,params := params tiles,block := HopperStage.block} trace.oracle code trace.count {} =
      .ok (trace.final,trace.events) at hs
    rw [hid] at hs
    obtain ⟨retries,_,_,_,_,he⟩ := completed_positive_source_reconstruct ht hb hs (hc trace hm).1
    exact ⟨trace.oracle,retries,trace,hm,hid,rfl,he⟩
  choose replies schedules traces hm hid hor he using hex
  exact ⟨⟨replies,schedules,traces,hm,hid,hor,he⟩⟩

theorem family_event_at {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (lane : Wgmma.Lane) (index : Nat) (event : Wgmma.Event)
    (he : (replyPositiveEvents tiles lane (family.replies lane) (family.schedules lane))[index]? = some event) :
    candidate.eventAt ⟨(ctx tiles lane).id,index⟩ = some event := by
  have hh := Unified.eventAt_of_member hw.2.1 (family.members lane) (serial := index)
  rw [family.ids lane,family.events lane] at hh
  exact hh.trans he

theorem family_wait_at {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) :
    candidate.eventAt (family.waitId tile lane) =
      some (waitEvent (ctx tiles lane) (barrierAddress (stage tile)) (expectedParity tile) true) :=
  family_event_at family hw lane _ _ (reply_complete_wait_at tiles lane (family.replies lane) (family.schedules lane) tile ht)

theorem family_failed_wait_at {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane)
    (attempt : Nat) (ha : attempt < family.schedules lane tile) :
    candidate.eventAt (family.failedWaitId tile lane attempt) =
      some (waitEvent (ctx tiles lane) (barrierAddress (stage tile)) (expectedParity tile) false) :=
  family_event_at family hw lane _ _ (reply_complete_failed_wait_at tiles lane (family.replies lane) (family.schedules lane) tile attempt ht ha)

theorem family_mma_at {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) :
    candidate.eventAt (family.mmaId tile lane) = some (.mma (family.marks tile lane) (family.calls tile lane)) :=
  family_event_at family hw lane _ _ (reply_complete_mma_at tiles lane (family.replies lane) (family.schedules lane) tile ht)

def familyCollective {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) :
    Unified.Collective candidate (family.mmaId tile 0) := {
  calls := family.calls tile
  marks := family.marks tile
  sources := family.mmaId tile
  representative := rfl
  matched := family_mma_at family hw tile ht
  sameCTA := fun _ => rfl
  sameMark := fun lane => (reply_mark_value tiles lane (family.replies lane) (family.schedules lane) tile).trans
    (reply_mark_value tiles 0 (family.replies 0) (family.schedules 0) tile).symm
  cohort := reply_calls_cohort tiles tile family.replies family.schedules
}

theorem completed_candidate_has_collective {tiles initial candidate} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (tile : Nat) (ht : tile < tiles) : ∃ issue, Nonempty (Unified.Collective candidate issue) := by
  obtain ⟨family⟩ := completed_candidate_reply_family (by omega) hb hw hc
  exact ⟨family.mmaId tile 0,⟨familyCollective family hw tile ht⟩⟩

theorem family_wait_before_mma {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) :
    Access.GenericAfter candidate.view (family.waitId tile lane) (family.mmaId tile lane) := by
  have hwait := family_wait_at family hw tile ht lane
  have hmma := family_mma_at family hw tile ht lane
  have horder := reply_wait_before_mma tiles lane (family.replies lane) (family.schedules lane) tile
  apply Ptx.Event.Path.single
  apply Or.inl
  refine ⟨?_,?_,horder.1,horder.2⟩
  · simp only [Hopper.Candidate.Present,Unified.view_eventAt,hwait,Option.map_some,Option.isSome_some]
  · simp only [Hopper.Candidate.Present,Unified.view_eventAt,hmma,Option.map_some,Option.isSome_some]

theorem family_failed_wait_not_observed {tiles initial candidate histories cluster copy} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane)
    (attempt : Nat) (ha : attempt < family.schedules lane tile) :
    ¬Access.CompletionObserved Tma.localShared candidate.view histories cluster copy (family.failedWaitId tile lane attempt) := by
  intro ho
  obtain ⟨loc,op,parity,before,after,ni,wi,_,_,hs,_⟩ := Access.observed_has_actual_notification ho
  have he := family_failed_wait_at family hw tile ht lane attempt ha
  have hf : candidate.view.barrierAt (family.failedWaitId tile lane attempt) =
      some ⟨⟨.shared .zero,barrierAddress (stage tile)⟩,.tryWaitParity (expectedParity tile) false⟩ := by
    simp only [Hopper.Candidate.barrierAt,Unified.view_eventAt,he,Option.map_some,waitEvent,Unified.eventView,Option.bind_some]
    rfl
  rw [hf] at hs
  cases hs

theorem family_tma_ready_from_observation {tiles initial candidate histories cluster copy offset operand loc}
    (family : ReplySourceFamily tiles candidate) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (tile : Nat) (ht : tile < tiles)
    (hl : Tma.writeLocation Tma.localShared candidate.view copy offset = some loc)
    (ho : Wgmma.operandLocation .zero (family.calls tile 0) operand = loc)
    (hobs : ∀ lane, Access.CompletionObserved Tma.localShared candidate.view histories cluster copy (family.waitId tile lane)) :
    Unified.TmaReady Tma.localShared candidate histories cluster copy offset (family.mmaId tile 0) operand loc :=
  ⟨familyCollective family hw tile ht,hl,ho,
    fun lane => ⟨family.waitId tile lane,hobs lane,family_wait_before_mma family hw tile ht lane⟩⟩

end
end Ptx.Kernels.HopperDoubleBuffer
