import Ptx.Kernels.HopperDoubleBufferReplyCandidate

/-! Rich source-event locations with arbitrary per-tile failed waits and
captured replies. Indices follow actual event-list prefixes; no fixed retry
count, collective admission or resource/memory observation is assumed. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def preludeEventCount (tile tiles : Nat) (leader : Bool) : Nat := if needsPrefetch tile tiles leader then 3 else 0
def replyTileCheckpoint (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) (tile : Nat) : LoopCheckpoint :=
  loopCheckpoint (ctx tiles lane) reply 0 tiles (HopperStage.leader lane) retries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) tile
def replyInitialEvents (lane : Wgmma.Lane) (reply : Wgmma.Oracle) : List Wgmma.Event :=
  initializationEvents (HopperStage.leader lane)++replyInitialCopies reply (HopperStage.leader lane)
def replyLoopEvents (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) (n : Nat) : List Wgmma.Event :=
  loopEvents (ctx tiles lane) reply 0 tiles (HopperStage.leader lane) retries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224 n
def replyIterationEvents (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) (tile : Nat) : List Wgmma.Event :=
  iterationEvents (ctx tiles lane) reply (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile)
    (HopperStage.leader lane) 4096 4224 (replyTileCheckpoint tiles lane reply retries tile).2
def replyCall (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) (tile : Nat) : Wgmma.Call :=
  computeCall (ctx tiles lane) reply (preparedState (replyTileCheckpoint tiles lane reply retries tile).1
    tile tiles (retries tile) (HopperStage.leader lane)) (aDescriptor (stage tile)) (bDescriptor (stage tile))
    (replyTileCheckpoint tiles lane reply retries tile).2
def replyMark (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) (tile : Nat) : Wgmma.Mark :=
  Wgmma.mark (ctx tiles lane) (computeFence (preparedState (replyTileCheckpoint tiles lane reply retries tile).1
    tile tiles (retries tile) (HopperStage.leader lane)))
def replyTileStart (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) (tile : Nat) : Nat :=
  (replyInitialEvents lane reply).length+(replyLoopEvents tiles lane reply retries tile).length
def replyFailedWaitId (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) (tile attempt : Nat) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,replyTileStart tiles lane reply retries tile+attempt⟩
def replyWaitId (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) (tile : Nat) : Ptx.Event.EventId :=
  replyFailedWaitId tiles lane reply retries tile (retries tile)
def replyMmaId (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) (tile : Nat) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,replyTileStart tiles lane reply retries tile+retries tile+preludeEventCount tile tiles (HopperStage.leader lane)+2⟩

theorem prelude_events_length (context reply s tile tiles leader mapA mapB) :
    (preludeEvents context reply s tile tiles leader mapA mapB).length = preludeEventCount tile tiles leader := by
  by_cases h : needsPrefetch tile tiles leader <;> simp [preludeEvents,preludeEventCount,h,prefetchTransferEvents]

theorem iteration_events_length (context reply s tile tiles retries leader mapA mapB values) :
    (iterationEvents context reply s tile tiles retries leader mapA mapB values).length = retries+preludeEventCount tile tiles leader+7 := by
  simp only [iterationEvents,List.length_append,List.length_replicate,List.length_cons,List.length_nil,
    prelude_events_length,computeEvents,advanceEvents]
  omega

theorem iteration_failed_wait_at (context reply s tile tiles retries leader mapA mapB values attempt) (ha : attempt < retries) :
    (iterationEvents context reply s tile tiles retries leader mapA mapB values)[attempt]? =
      some (waitEvent context (barrierAddress (stage tile)) (expectedParity tile) false) := by
  simp only [iterationEvents,List.append_assoc]
  rw [List.getElem?_append_left (by simpa only [List.length_replicate] using ha)]
  simp [ha]

theorem iteration_successful_wait_at (context reply s tile tiles retries leader mapA mapB values) :
    (iterationEvents context reply s tile tiles retries leader mapA mapB values)[retries]? =
      some (waitEvent context (barrierAddress (stage tile)) (expectedParity tile) true) := by
  simp only [iterationEvents,List.append_assoc]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem iteration_mma_at (context reply s tile tiles retries leader mapA mapB values) :
    (iterationEvents context reply s tile tiles retries leader mapA mapB values)[retries+preludeEventCount tile tiles leader+2]? =
      some (.mma (Wgmma.mark context (computeFence (preparedState s tile tiles retries leader)))
        (computeCall context reply (preparedState s tile tiles retries leader) (aDescriptor (stage tile)) (bDescriptor (stage tile)) values)) := by
  simp only [iterationEvents,List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_singleton]
  rw [List.getElem?_append_right (by rw [prelude_events_length]; omega),prelude_events_length]
  rw [show retries+preludeEventCount tile tiles leader+2-retries-1-preludeEventCount tile tiles leader = 1 by omega]
  rfl

theorem reply_loop_index_retained (tiles lane reply retries) (m n index : Nat) (event : Wgmma.Event) (hle : m ≤ n)
    (he : (replyLoopEvents tiles lane reply retries m)[index]? = some event) :
    (replyLoopEvents tiles lane reply retries n)[index]? = some event := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    simpa only [hm] using he
  | succ n ih =>
    by_cases hm : m = n+1
    · simpa only [hm] using he
    · have hold := ih (by omega)
      have hi := (List.getElem?_eq_some_iff.mp hold).1
      unfold replyLoopEvents at hi
      simp only [replyLoopEvents,loopEvents]
      rw [List.getElem?_append_left hi]
      exact hold

theorem reply_complete_iteration_at (tiles lane reply retries tile index event) (ht : tile < tiles)
    (he : (replyIterationEvents tiles lane reply retries tile)[index]? = some event) :
    (replyPositiveEvents tiles lane reply retries)[replyTileStart tiles lane reply retries tile+index]? = some event := by
  have hs : (replyLoopEvents tiles lane reply retries (tile+1))[(replyLoopEvents tiles lane reply retries tile).length+index]? = some event := by
    simp only [replyLoopEvents,loopEvents,Nat.zero_add]
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    exact he
  have hf := reply_loop_index_retained tiles lane reply retries (tile+1) tiles _ event (by omega) hs
  have hi := (List.getElem?_eq_some_iff.mp hf).1
  simp only [replyPositiveEvents,← List.append_assoc]
  change ((replyInitialEvents lane reply++replyLoopEvents tiles lane reply retries tiles)++_)[replyTileStart tiles lane reply retries tile+index]? = _
  rw [List.getElem?_append_left (by simp only [List.length_append]; unfold replyTileStart; omega)]
  rw [List.getElem?_append_right (by unfold replyTileStart; omega)]
  simpa only [replyTileStart,Nat.add_assoc,Nat.add_sub_cancel_left] using hf

theorem reply_complete_failed_wait_at (tiles lane reply retries tile attempt) (ht : tile < tiles) (ha : attempt < retries tile) :
    (replyPositiveEvents tiles lane reply retries)[(replyFailedWaitId tiles lane reply retries tile attempt).serial]? =
      some (waitEvent (ctx tiles lane) (barrierAddress (stage tile)) (expectedParity tile) false) :=
  reply_complete_iteration_at tiles lane reply retries tile attempt _ ht (iteration_failed_wait_at _ _ _ _ _ _ _ _ _ _ _ ha)

theorem reply_complete_wait_at (tiles lane reply retries tile) (ht : tile < tiles) :
    (replyPositiveEvents tiles lane reply retries)[(replyWaitId tiles lane reply retries tile).serial]? =
      some (waitEvent (ctx tiles lane) (barrierAddress (stage tile)) (expectedParity tile) true) :=
  reply_complete_iteration_at tiles lane reply retries tile (retries tile) _ ht (iteration_successful_wait_at _ _ _ _ _ _ _ _ _ _)

theorem reply_complete_mma_at (tiles lane reply retries tile) (ht : tile < tiles) :
    (replyPositiveEvents tiles lane reply retries)[(replyMmaId tiles lane reply retries tile).serial]? =
      some (.mma (replyMark tiles lane reply retries tile) (replyCall tiles lane reply retries tile)) := by
  have hh := reply_complete_iteration_at tiles lane reply retries tile _ _ ht
    (iteration_mma_at (ctx tiles lane) reply (replyTileCheckpoint tiles lane reply retries tile).1 tile tiles (retries tile)
      (HopperStage.leader lane) 4096 4224 (replyTileCheckpoint tiles lane reply retries tile).2)
  simpa only [replyMmaId,replyMark,replyCall,Nat.add_assoc] using hh

theorem reply_wait_before_mma (tiles lane reply retries tile) :
    (replyWaitId tiles lane reply retries tile).thread = (replyMmaId tiles lane reply retries tile).thread ∧
      (replyWaitId tiles lane reply retries tile).serial < (replyMmaId tiles lane reply retries tile).serial := by
  refine ⟨rfl,?_⟩
  dsimp only [replyWaitId,replyFailedWaitId,replyMmaId]
  omega

end
end Ptx.Kernels.HopperDoubleBuffer
