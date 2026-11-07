import Ptx.Kernels.HopperDoubleBufferRetryResourceCases

/-! Exhaustive rich source classification through initial/loop/output pieces
and all candidate threads. No selected retry schedule, descriptor/payload value
or resource-history membership is assumed by the classification. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_initial_resource_case {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane)
    (ht : 0 < tiles) (index : Nat) (event : Wgmma.Event)
    (he : (replyInitialEvents lane (family.replies lane))[index]? = some event) (hr : isResourceEvent event = true) :
    RetryResourceSource family ⟨(ctx tiles lane).id,index⟩ event := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  cases hl : HopperStage.leader lane
  · have hb : index < 2 := by simpa only [replyInitialEvents,hl,initializationEvents,replyInitialCopies,Bool.false_eq_true,ite_false,
        List.nil_append,List.append_nil,List.length_cons,List.length_nil] using hi
    interval_cases index
    all_goals simp only [replyInitialEvents,hl,initializationEvents,replyInitialCopies,Bool.false_eq_true,ite_false,
      List.nil_append,List.append_nil,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    all_goals cases he; cases hr
  · have hz : lane = 0 := (leader_iff_zero lane).mp hl
    subst lane
    have hb : index < 8 := hi
    interval_cases index
    · cases he; exact RetryResourceSource.init 0
    · cases he; exact RetryResourceSource.init 1
    · cases he; cases hr
    · cases he; cases hr
    · cases he; cases hr
    · cases he; exact RetryResourceSource.expect 0 ht
    · cases he; exact RetryResourceSource.copyA 0 ht
    · cases he; exact RetryResourceSource.copyB 0 ht

theorem retry_loop_resource_case {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane) (n : Nat)
    (hn : n ≤ tiles) (index : Nat) (event : Wgmma.Event)
    (he : (replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) n)[index]? = some event)
    (hr : isResourceEvent event = true) :
    RetryResourceSource family ⟨(ctx tiles lane).id,(replyInitialEvents lane (family.replies lane)).length+index⟩ event := by
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
      have hc := retry_iteration_resource_case family n lane (by omega)
        (index-(replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) n).length) event he hr
      have hindex : replyTileStart tiles lane (family.replies lane) (family.schedules lane) n+
          (index-(replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) n).length) =
          (replyInitialEvents lane (family.replies lane)).length+index := by unfold replyTileStart; omega
      simpa only [hindex] using hc

theorem retry_output_resource_case {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane)
    (index : Nat) (event : Wgmma.Event)
    (he : (outputEvents (ctx tiles lane) (replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).1 lane
      (HopperStage.leader lane) (replyCheckpoint tiles lane (family.replies lane) (family.schedules lane)).2)[index]? = some event)
    (hr : isResourceEvent event = true) :
    RetryResourceSource family ⟨(ctx tiles lane).id,replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles+index⟩ event := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  cases hl : HopperStage.leader lane
  · have hb : index < 6 := by simpa only [outputEvents,returnEvents,hl,Bool.false_eq_true,ite_false,
        List.length_append,outputWriteEvents,List.length_cons,List.length_nil] using hi
    interval_cases index
    all_goals simp only [outputEvents,returnEvents,hl,Bool.false_eq_true,ite_false,outputWriteEvents,
      List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    all_goals cases he; cases hr
  · have hz : lane = 0 := (leader_iff_zero lane).mp hl
    subst lane
    have hb : index < 8 := by simpa only [outputEvents,returnEvents,hl,ite_true,
        List.length_append,outputWriteEvents,List.length_cons,List.length_nil] using hi
    interval_cases index
    all_goals first
      | (cases he; exact RetryResourceSource.inval 0)
      | (cases he; exact RetryResourceSource.inval 1)
      | (simp only [outputEvents,returnEvents,hl,ite_true,outputWriteEvents,
          List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
         cases he
         cases hr)

theorem retry_complete_resource_case {tiles candidate} (family : ReplySourceFamily tiles candidate) (lane : Wgmma.Lane)
    (ht : 0 < tiles) (index : Nat) (event : Wgmma.Event)
    (he : (replyPositiveEvents tiles lane (family.replies lane) (family.schedules lane))[index]? = some event)
    (hr : isResourceEvent event = true) : RetryResourceSource family ⟨(ctx tiles lane).id,index⟩ event := by
  simp only [replyPositiveEvents,← List.append_assoc] at he
  change ((replyInitialEvents lane (family.replies lane)++replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) tiles)++_)[index]? = some event at he
  by_cases hi : index < replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles
  · rw [List.getElem?_append_left (by simpa only [List.length_append,replyTileStart] using hi)] at he
    by_cases hinitial : index < (replyInitialEvents lane (family.replies lane)).length
    · rw [List.getElem?_append_left hinitial] at he
      exact retry_initial_resource_case family lane ht index event he hr
    · rw [List.getElem?_append_right (by omega)] at he
      have hc := retry_loop_resource_case family lane tiles (Nat.le_refl _)
        (index-(replyInitialEvents lane (family.replies lane)).length) event he hr
      simpa only [show (replyInitialEvents lane (family.replies lane)).length+
        (index-(replyInitialEvents lane (family.replies lane)).length) = index by omega] using hc
  · rw [List.getElem?_append_right (by simpa only [List.length_append,replyTileStart] using Nat.le_of_not_gt hi)] at he
    have hc := retry_output_resource_case family lane
      (index-(replyInitialEvents lane (family.replies lane)++replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) tiles).length) event he hr
    have hindex : replyTileStart tiles lane (family.replies lane) (family.schedules lane) tiles+
        (index-(replyInitialEvents lane (family.replies lane)++replyLoopEvents tiles lane (family.replies lane) (family.schedules lane) tiles).length) = index := by
      simp only [List.length_append,replyTileStart]
      unfold replyTileStart at hi
      omega
    simpa only [hindex] using hc

theorem retry_candidate_resource_case {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (id : Ptx.Event.EventId) (event : Wgmma.Event)
    (he : candidate.eventAt id = some event) (hr : isResourceEvent event = true) : RetryResourceSource family id event := by
  obtain ⟨trace,hm,hid,_⟩ := Unified.eventAt_trace he
  obtain ⟨lane,hlane⟩ := HopperStage.ctx_covered (hw.2.2.1 trace hm).1
  change (ctx tiles lane).id = trace.id at hlane
  cases id with
  | mk thread serial =>
    change trace.id = thread at hid
    have hs : thread = (ctx tiles lane).id := (hlane.trans hid).symm
    rw [hs] at he ⊢
    have hh := Unified.eventAt_of_member hw.2.1 (family.members lane) (serial := serial)
    rw [family.ids lane,family.events lane] at hh
    exact retry_complete_resource_case family lane ht serial event (hh.symm.trans he) hr

end
end Ptx.Kernels.HopperDoubleBuffer
