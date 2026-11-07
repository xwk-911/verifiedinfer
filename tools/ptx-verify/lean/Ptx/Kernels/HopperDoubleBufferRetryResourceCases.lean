import Ptx.Kernels.HopperDoubleBufferRetryObservations
import Ptx.Kernels.HopperDoubleBufferResourceCases

/-! Indexed resource classification with arbitrary rich replies and failed
waits. Cases come from source event lists, not history membership premises. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

inductive RetryResourceSource {tiles candidate} (family : ReplySourceFamily tiles candidate) : Ptx.Event.EventId → Wgmma.Event → Prop
  | init (slot : Stage) : RetryResourceSource family (family.initId slot) (.base (.barrier ⟨dataGate slot,.init 1⟩))
  | expect (tile : Nat) (ht : tile < tiles) : RetryResourceSource family (family.expectId tile)
      (.base (.barrier ⟨dataGate (stage tile),.arriveExpectTx 2304⟩))
  | failed (tile : Nat) (lane : Wgmma.Lane) (attempt : Nat) (ht : tile < tiles) (ha : attempt < family.schedules lane tile) :
      RetryResourceSource family (family.failedWaitId tile lane attempt)
        (waitEvent (ctx tiles lane) (barrierAddress (stage tile)) (expectedParity tile) false)
  | wait (tile : Nat) (lane : Wgmma.Lane) (ht : tile < tiles) : RetryResourceSource family (family.waitId tile lane)
      (waitEvent (ctx tiles lane) (barrierAddress (stage tile)) (expectedParity tile) true)
  | copyA (tile : Nat) (ht : tile < tiles) : RetryResourceSource family (family.copyAId tile).issue
      (.base (.tmaIssue (replyCopyA tiles (family.replies 0) (family.schedules 0) tile)))
  | copyB (tile : Nat) (ht : tile < tiles) : RetryResourceSource family (family.copyBId tile).issue
      (.base (.tmaIssue (replyCopyB tiles (family.replies 0) (family.schedules 0) tile)))
  | inval (slot : Stage) : RetryResourceSource family (family.invalId slot) (.base (.barrier ⟨dataGate slot,.inval⟩))

theorem compute_advance_no_resource (context reply s tile tiles retries leader values) :
    (computeEvents context reply (preparedState s tile tiles retries leader) (aDescriptor (stage tile)) (bDescriptor (stage tile)) values++
      advanceEvents (computeState context reply (preparedState s tile tiles retries leader) (aDescriptor (stage tile)) (bDescriptor (stage tile)) values)).all
        (fun event => !isResourceEvent event) = true := rfl

theorem retry_iteration_resource_index (context reply s tile tiles retries leader mapA mapB values)
    (index : Nat) (event : Wgmma.Event)
    (he : (iterationEvents context reply s tile tiles retries leader mapA mapB values)[index]? = some event)
    (hr : isResourceEvent event = true) :
    index ≤ retries ∨ (needsPrefetch tile tiles leader ∧ (index = retries+1 ∨ index = retries+2 ∨ index = retries+3)) := by
  by_cases hw : index ≤ retries
  · exact Or.inl hw
  · simp only [iterationEvents,List.append_assoc] at he
    rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega)] at he
    rw [List.getElem?_append_right (by simp only [List.length_replicate,List.length_cons,List.length_nil]; omega)] at he
    simp only [List.length_replicate,List.length_cons,List.length_nil] at he
    by_cases hp : index-retries-1 < (preludeEvents context reply (headerState s tile retries) tile tiles leader mapA mapB).length
    · have hb := hp
      rw [prelude_events_length] at hb
      by_cases hn : needsPrefetch tile tiles leader
      · simp only [preludeEventCount,hn,ite_true] at hb
        exact Or.inr ⟨hn,by omega⟩
      · simp only [preludeEventCount,hn,ite_false] at hb
        omega
    · rw [List.getElem?_append_right (by omega)] at he
      have hn := List.all_eq_true.mp (compute_advance_no_resource context reply s tile tiles retries leader values)
        event (List.mem_of_getElem? he)
      simp only [hr,Bool.not_true] at hn
      cases hn

theorem retry_iteration_resource_case {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane)
    (ht : tile < tiles) (index : Nat) (event : Wgmma.Event)
    (he : (replyIterationEvents tiles lane (family.replies lane) (family.schedules lane) tile)[index]? = some event)
    (hr : isResourceEvent event = true) :
    RetryResourceSource family ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+index⟩ event := by
  rcases retry_iteration_resource_index _ _ _ _ _ _ _ _ _ _ index event he hr with hw | ⟨hn,hi⟩
  · by_cases hf : index < family.schedules lane tile
    · have hv := iteration_failed_wait_at (ctx tiles lane) (family.replies lane)
        (replyTileCheckpoint tiles lane (family.replies lane) (family.schedules lane) tile).1 tile tiles
        (family.schedules lane tile) (HopperStage.leader lane) 4096 4224
        (replyTileCheckpoint tiles lane (family.replies lane) (family.schedules lane) tile).2 index hf
      cases Option.some.inj (he.symm.trans hv)
      exact RetryResourceSource.failed tile lane index ht hf
    · have hi : index = family.schedules lane tile := by omega
      subst index
      have hv := iteration_successful_wait_at (ctx tiles lane) (family.replies lane)
        (replyTileCheckpoint tiles lane (family.replies lane) (family.schedules lane) tile).1 tile tiles
        (family.schedules lane tile) (HopperStage.leader lane) 4096 4224
        (replyTileCheckpoint tiles lane (family.replies lane) (family.schedules lane) tile).2
      cases Option.some.inj (he.symm.trans hv)
      exact RetryResourceSource.wait tile lane ht
  · have hl : lane = 0 := (leader_iff_zero lane).mp hn.2
    subst lane
    have getPrefetch (offset : Nat) (ho : offset < 3) :
        (replyIterationEvents tiles 0 (family.replies 0) (family.schedules 0) tile)[family.schedules 0 tile+1+offset]? =
          (prefetchTransferEvents (ctx tiles 0) (family.replies 0)
            (replyPrefetchState tiles (family.replies 0) (family.schedules 0) tile) (stage (tile+1)) (tile+1) 4096 4224)[offset]? :=
      iteration_prefetch_at _ _ _ _ _ _ _ _ _ _ offset hn ho
    rcases hi with rfl | rfl | rfl
    · have hv := getPrefetch 0 (by decide)
      simp only [Nat.add_zero] at hv
      rw [he] at hv
      cases Option.some.inj hv
      simpa only [ReplySourceFamily.expectId,replyExpectId,replyPrefetchId,Nat.add_zero,Nat.add_assoc,dataGate,ctx,HopperStage.ctx] using
        RetryResourceSource.expect (family := family) (tile+1) hn.1
    · have hv := getPrefetch 1 (by decide)
      rw [show family.schedules 0 tile+1+1 = family.schedules 0 tile+2 by omega,he] at hv
      cases Option.some.inj hv
      simpa only [ReplySourceFamily.copyAId,replyCopyAId,replyPrefetchId,replyCopyA,Nat.add_assoc,Nat.reduceAdd] using
        RetryResourceSource.copyA (family := family) (tile+1) hn.1
    · have hv := getPrefetch 2 (by decide)
      rw [show family.schedules 0 tile+1+2 = family.schedules 0 tile+3 by omega,he] at hv
      cases Option.some.inj hv
      simpa only [ReplySourceFamily.copyBId,replyCopyBId,replyPrefetchId,replyCopyB,Nat.add_assoc,Nat.reduceAdd] using
        RetryResourceSource.copyB (family := family) (tile+1) hn.1

end
end Ptx.Kernels.HopperDoubleBuffer
