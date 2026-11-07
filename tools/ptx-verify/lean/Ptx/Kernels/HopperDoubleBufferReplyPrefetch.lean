import Ptx.Kernels.HopperDoubleBufferCandidateCollective

/-! Actual expectation and TMA issue identities for every tile, including
prefetches after arbitrary failed waits. Captured descriptors and payloads
are preserved. Source issue/order is separate from completion, visibility,
resource-history admission and numerical correctness. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def replyPrefetchState (tiles : Nat) (reply : Wgmma.Oracle) (retries : Nat → Nat) (tile : Nat) : Wgmma.State :=
  prefetchGuardState (headerState (replyTileCheckpoint tiles 0 reply retries tile).1 tile (retries tile)) tile tiles true
def replyPrefetchId (tiles : Nat) (reply : Wgmma.Oracle) (retries : Nat → Nat) (tile index : Nat) : Ptx.Event.EventId :=
  ⟨(ctx tiles 0).id,replyTileStart tiles 0 reply retries tile+retries tile+1+index⟩
def replyExpectId (tiles : Nat) (reply : Wgmma.Oracle) (retries : Nat → Nat) : Nat → Ptx.Event.EventId
  | 0 => ⟨(ctx tiles 0).id,5⟩
  | tile+1 => replyPrefetchId tiles reply retries tile 0
def replyCopyAId (tiles : Nat) (reply : Wgmma.Oracle) (retries : Nat → Nat) : Nat → Tma.CopyId
  | 0 => ⟨⟨(ctx tiles 0).id,6⟩⟩
  | tile+1 => ⟨replyPrefetchId tiles reply retries tile 1⟩
def replyCopyBId (tiles : Nat) (reply : Wgmma.Oracle) (retries : Nat → Nat) : Nat → Tma.CopyId
  | 0 => ⟨⟨(ctx tiles 0).id,7⟩⟩
  | tile+1 => ⟨replyPrefetchId tiles reply retries tile 2⟩
def replyCopyA (tiles : Nat) (reply : Wgmma.Oracle) (retries : Nat → Nat) : Nat → TmaCopy
  | 0 => replyInitialA reply
  | tile+1 => prefetchACopy reply (replyPrefetchState tiles reply retries tile) (stage (tile+1)) (tile+1) 4096
def replyCopyB (tiles : Nat) (reply : Wgmma.Oracle) (retries : Nat → Nat) : Nat → TmaCopy
  | 0 => replyInitialB reply
  | tile+1 => prefetchBCopy reply (replyPrefetchState tiles reply retries tile) (stage (tile+1)) (tile+1) 4224

theorem iteration_prefetch_at (context reply s tile tiles retries leader mapA mapB values index)
    (hn : needsPrefetch tile tiles leader) (hi : index < 3) :
    (iterationEvents context reply s tile tiles retries leader mapA mapB values)[retries+1+index]? =
      (prefetchTransferEvents context reply (prefetchGuardState (headerState s tile retries) tile tiles leader)
        (stage (tile+1)) (tile+1) mapA mapB)[index]? := by
  simp only [iterationEvents,List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_singleton]
  rw [List.getElem?_append_left (by rw [prelude_events_length]; simp [preludeEventCount,hn]; omega)]
  rw [show retries+1+index-retries-1 = index by omega]
  simp only [preludeEvents,hn,ite_true]

theorem reply_complete_initial_at (tiles lane reply retries) (index : Nat) (event : Wgmma.Event)
    (he : (replyInitialEvents lane reply)[index]? = some event) :
    (replyPositiveEvents tiles lane reply retries)[index]? = some event := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  simp only [replyPositiveEvents,← List.append_assoc]
  change ((replyInitialEvents lane reply++replyLoopEvents tiles lane reply retries tiles)++_)[index]? = _
  rw [List.getElem?_append_left (by simp only [List.length_append]; omega)]
  rw [List.getElem?_append_left hi]
  exact he

theorem reply_complete_prefetch_at (tiles reply retries tile index event) (ht : tile+1 < tiles) (hi : index < 3)
    (he : (prefetchTransferEvents (ctx tiles 0) reply (replyPrefetchState tiles reply retries tile)
      (stage (tile+1)) (tile+1) 4096 4224)[index]? = some event) :
    (replyPositiveEvents tiles 0 reply retries)[(replyPrefetchId tiles reply retries tile index).serial]? = some event := by
  have hn : needsPrefetch tile tiles (HopperStage.leader (0 : Wgmma.Lane)) := ⟨ht,rfl⟩
  have hh := iteration_prefetch_at (ctx tiles 0) reply (replyTileCheckpoint tiles 0 reply retries tile).1
    tile tiles (retries tile) (HopperStage.leader 0) 4096 4224
    (replyTileCheckpoint tiles 0 reply retries tile).2 index hn hi
  have hl := reply_complete_iteration_at tiles 0 reply retries tile _ event (by omega) (hh.trans he)
  simpa only [replyPrefetchId,Nat.add_assoc] using hl

theorem reply_complete_expect_at (tiles reply retries tile) (ht : tile < tiles) :
    (replyPositiveEvents tiles 0 reply retries)[(replyExpectId tiles reply retries tile).serial]? =
      some (.base (.barrier ⟨⟨.shared .zero,barrierAddress (stage tile)⟩,.arriveExpectTx 2304⟩)) := by
  cases tile with
  | zero => exact reply_complete_initial_at tiles 0 reply retries 5 _ (by rfl)
  | succ tile => exact reply_complete_prefetch_at tiles reply retries tile 0 _ ht (by decide) rfl

theorem reply_complete_copy_a_at (tiles reply retries tile) (ht : tile < tiles) :
    (replyPositiveEvents tiles 0 reply retries)[(replyCopyAId tiles reply retries tile).issue.serial]? =
      some (.base (.tmaIssue (replyCopyA tiles reply retries tile))) := by
  cases tile with
  | zero => exact reply_complete_initial_at tiles 0 reply retries 6 _ (by rfl)
  | succ tile => exact reply_complete_prefetch_at tiles reply retries tile 1 _ ht (by decide) rfl

theorem reply_complete_copy_b_at (tiles reply retries tile) (ht : tile < tiles) :
    (replyPositiveEvents tiles 0 reply retries)[(replyCopyBId tiles reply retries tile).issue.serial]? =
      some (.base (.tmaIssue (replyCopyB tiles reply retries tile))) := by
  cases tile with
  | zero => exact reply_complete_initial_at tiles 0 reply retries 7 _ (by rfl)
  | succ tile => exact reply_complete_prefetch_at tiles reply retries tile 2 _ ht (by decide) rfl

theorem reply_expect_copy_source_order (tiles reply retries tile) :
    (replyExpectId tiles reply retries tile).thread = (replyCopyAId tiles reply retries tile).issue.thread ∧
    (replyCopyAId tiles reply retries tile).issue.thread = (replyCopyBId tiles reply retries tile).issue.thread ∧
    (replyExpectId tiles reply retries tile).serial < (replyCopyAId tiles reply retries tile).issue.serial ∧
    (replyCopyAId tiles reply retries tile).issue.serial < (replyCopyBId tiles reply retries tile).issue.serial := by
  cases tile <;> simp [replyExpectId,replyCopyAId,replyCopyBId,replyPrefetchId]

theorem reply_tile_start_succ (tiles lane reply retries tile) :
    replyTileStart tiles lane reply retries (tile+1) = replyTileStart tiles lane reply retries tile+
      retries tile+preludeEventCount tile tiles (HopperStage.leader lane)+7 := by
  simp only [replyTileStart,replyLoopEvents,loopEvents,List.length_append,iteration_events_length,Nat.zero_add]
  omega

theorem reply_copy_before_producer_wait (tiles reply retries tile) :
    (replyCopyBId tiles reply retries tile).issue.thread = (replyWaitId tiles 0 reply retries tile).thread ∧
    (replyCopyBId tiles reply retries tile).issue.serial < (replyWaitId tiles 0 reply retries tile).serial := by
  cases tile with
  | zero =>
    constructor
    · rfl
    · change 7 < (replyInitialEvents 0 reply).length+0+retries 0
      have hi : (replyInitialEvents 0 reply).length = 8 := rfl
      omega
  | succ tile =>
    constructor
    · rfl
    · simp only [replyCopyBId,replyPrefetchId,replyWaitId,replyFailedWaitId,reply_tile_start_succ]
      omega

theorem reply_prefetch_queries (tiles reply retries tile) :
    (replyPrefetchState tiles reply retries tile).base.scalar.core.queries =
      loopQuery 0 tiles true retries 4 tile+retries tile+1 := by
  simp only [replyPrefetchState,prefetchGuardState_queries,headerState_queries,replyTileCheckpoint,loopCheckpoint_queries]
  rfl

def ReplySourceFamily.expectId {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) : Ptx.Event.EventId :=
  replyExpectId tiles (family.replies 0) (family.schedules 0) tile
def ReplySourceFamily.copyAId {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) : Tma.CopyId :=
  replyCopyAId tiles (family.replies 0) (family.schedules 0) tile
def ReplySourceFamily.copyBId {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) : Tma.CopyId :=
  replyCopyBId tiles (family.replies 0) (family.schedules 0) tile

theorem family_expect_at {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) :
    candidate.view.barrierAt (family.expectId tile) =
      some ⟨⟨.shared .zero,barrierAddress (stage tile)⟩,.arriveExpectTx 2304⟩ := by
  have he := family_event_at family hw 0 _ _ (reply_complete_expect_at tiles (family.replies 0) (family.schedules 0) tile ht)
  have hid : (⟨(ctx tiles 0).id,(replyExpectId tiles (family.replies 0) (family.schedules 0) tile).serial⟩ : Ptx.Event.EventId) =
      family.expectId tile := by cases tile <;> rfl
  rw [hid] at he
  simp only [Hopper.Candidate.barrierAt,Unified.view_eventAt,he,Option.map_some,Unified.eventView,Option.bind_some]

theorem family_copy_a_at {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) :
    Tma.copyAt candidate.view (family.copyAId tile) = some (replyCopyA tiles (family.replies 0) (family.schedules 0) tile) := by
  have he := family_event_at family hw 0 _ _ (reply_complete_copy_a_at tiles (family.replies 0) (family.schedules 0) tile ht)
  have hid : (⟨(ctx tiles 0).id,(replyCopyAId tiles (family.replies 0) (family.schedules 0) tile).issue.serial⟩ : Ptx.Event.EventId) =
      (family.copyAId tile).issue := by cases tile <;> rfl
  rw [hid] at he
  simp only [Tma.copyAt,Unified.view_eventAt,he,Option.map_some,Unified.eventView,Option.bind_some]

theorem family_copy_b_at {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) :
    Tma.copyAt candidate.view (family.copyBId tile) = some (replyCopyB tiles (family.replies 0) (family.schedules 0) tile) := by
  have he := family_event_at family hw 0 _ _ (reply_complete_copy_b_at tiles (family.replies 0) (family.schedules 0) tile ht)
  have hid : (⟨(ctx tiles 0).id,(replyCopyBId tiles (family.replies 0) (family.schedules 0) tile).issue.serial⟩ : Ptx.Event.EventId) =
      (family.copyBId tile).issue := by cases tile <;> rfl
  rw [hid] at he
  simp only [Tma.copyAt,Unified.view_eventAt,he,Option.map_some,Unified.eventView,Option.bind_some]

end
end Ptx.Kernels.HopperDoubleBuffer
