import Ptx.Kernels.HopperDoubleBufferRetryArbitraryObservations
import Ptx.Tests.HopperPrefixAccounting

/-! Arbitrary-history completion phases and actual negative histories. The
negative-debt history preserves protocol/source/inventory checks but fails
unified control. Existing joint components establish positive nonvacuity. -/
namespace Ptx.HopperArbitraryObservationTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev family (a b) := HopperPrefixAccountingTests.family a b
abbrev candidate (a b) := HopperPrefixAccountingTests.candidate a b
abbrev source (a b) := HopperPrefixAccountingTests.source a b
abbrev descriptors (a b) := HopperPrefixAccountingTests.descriptors a b
abbrev valid (a b) := retry_all_histories_valid (family a b) (by decide) (source a b) (descriptors a b)
abbrev acyclic (a b) := retry_unified_control_acyclic (family a b) (by decide) (by decide) (source a b)

theorem all_histories_exact_wait (a b) (histories : Location → List Tma.Entry)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared (candidate a b).view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block (candidate a b) histories) (tile : Fin 3) (lane : Wgmma.Lane) :
    ∃ state, Mbarrier.run none (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
      (actualWaitIndex (family a b) histories tile lane)) = some (some state) ∧
      state.phase = tile.val/2+1 ∧ state.pending = 1 ∧ state.tx = 0 ∧
      Mbarrier.arrivalCount (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
        (actualWaitIndex (family a b) histories tile lane)) = tile.val/2+1 ∧
      Tma.stampBefore (histories (dataGate (stage tile))) (actualWaitIndex (family a b) histories tile lane) = some ⟨1,tile.val/2+1⟩ :=
  arbitrary_history_wait_state (family a b) (by decide) (source a b) (descriptors a b) hh hc tile tile.isLt lane

theorem all_histories_exact_notice (a b) (histories : Location → List Tma.Entry)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared (candidate a b).view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block (candidate a b) histories) (first : Bool) (tile : Fin 3) :
    ∃ state, Mbarrier.run none (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
      (actualNoticeIndex (family a b) histories first tile)) = some (some state) ∧
      state.phase = tile.val/2 ∧ state.pending = 0 ∧ 0 < state.tx ∧
      Tma.stampBefore (histories (dataGate (stage tile))) (actualNoticeIndex (family a b) histories first tile) = some ⟨1,tile.val/2⟩ :=
  arbitrary_history_notice_exact_phase (family a b) (by decide) (source a b) (descriptors a b) hh hc first tile tile.isLt

theorem all_histories_observation (a b) (histories : Location → List Tma.Entry)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared (candidate a b).view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block (candidate a b) histories) (first : Bool) (tile : Fin 3) (lane : Wgmma.Lane) :
    Tma.observation (histories (dataGate (stage tile))) (actualNoticeIndex (family a b) histories first tile)
      (actualWaitIndex (family a b) histories tile lane) = some (accountedCopyId (family a b) first tile,(family a b).waitId tile lane) :=
  arbitrary_history_observe (family a b) (by decide) (source a b) (descriptors a b) hh hc first tile tile.isLt lane

theorem all_histories_completion_edges (a b) (histories : Location → List Tma.Entry)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared (candidate a b).view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block (candidate a b) histories) (first : Bool) (tile : Fin 3) (lane : Wgmma.Lane) :
    Access.CompletionObserved Tma.localShared (candidate a b).view histories dataCluster
      (accountedCopyId (family a b) first tile) ((family a b).waitId tile lane) :=
  arbitrary_history_completion_observed (family a b) (by decide) (source a b) (descriptors a b) hh hc first tile tile.isLt lane

theorem positive_joint_observations (a b) (tile : Fin 3) (lane : Wgmma.Lane) :
    Access.CompletionObserved Tma.localShared (candidate a b).view (retryHistories (family a b)) dataCluster
      ((family a b).copyAId tile) ((family a b).waitId tile lane) ∧
    Access.CompletionObserved Tma.localShared (candidate a b).view (retryHistories (family a b)) dataCluster
      ((family a b).copyBId tile) ((family a b).waitId tile lane) := by
  obtain ⟨htma,hcontrol,_⟩ := retry_data_complete_components a b 3 HopperArbitraryHistoryTests.schedule
    HopperPrefixAccountingTests.initial (by decide) (by decide)
  exact arbitrary_histories_completion_observations (family a b) (by decide) htma hcontrol tile tile.isLt lane

theorem actual_first_wait_stamp (a b) (lane : Wgmma.Lane) :
    Tma.stampBefore (retryHistories (family a b) (dataGate 0))
      (actualWaitIndex (family a b) (retryHistories (family a b)) 0 lane) = some ⟨1,1⟩ := by
  obtain ⟨_,_,_,_,_,_,hs⟩ := all_histories_exact_wait a b _ (valid a b) (acyclic a b) 0 lane
  exact hs

theorem actual_reused_wait_stamp (a b) (lane : Wgmma.Lane) :
    Tma.stampBefore (retryHistories (family a b) (dataGate 0))
      (actualWaitIndex (family a b) (retryHistories (family a b)) 2 lane) = some ⟨1,2⟩ := by
  obtain ⟨_,_,_,_,_,_,hs⟩ := all_histories_exact_wait a b _ (valid a b) (acyclic a b) 2 lane
  exact hs

theorem actual_reused_notice_stamp (a b) (first : Bool) :
    Tma.stampBefore (retryHistories (family a b) (dataGate 0))
      (actualNoticeIndex (family a b) (retryHistories (family a b)) first 2) = some ⟨1,1⟩ := by
  obtain ⟨_,_,_,_,_,hs⟩ := all_histories_exact_notice a b _ (valid a b) (acyclic a b) first 2
  exact hs

theorem actual_old_notice_rejected (a b) (first : Bool) (lane : Wgmma.Lane) :
    Tma.observation (retryHistories (family a b) (dataGate 0))
      (actualNoticeIndex (family a b) (retryHistories (family a b)) first 0)
      (actualWaitIndex (family a b) (retryHistories (family a b)) 2 lane) = none :=
  arbitrary_history_wrong_tile_not_observed (family a b) (by decide) (source a b) (descriptors a b) (valid a b) (acyclic a b)
    first 0 2 (by decide) (by decide) (by decide) (by decide) lane

theorem actual_future_notice_rejected (a b) (first : Bool) (lane : Wgmma.Lane) :
    Tma.observation (retryHistories (family a b) (dataGate 0))
      (actualNoticeIndex (family a b) (retryHistories (family a b)) first 2)
      (actualWaitIndex (family a b) (retryHistories (family a b)) 0 lane) = none :=
  arbitrary_history_wrong_tile_not_observed (family a b) (by decide) (source a b) (descriptors a b) (valid a b) (acyclic a b)
    first 2 0 (by decide) (by decide) (by decide) (by decide) lane

theorem phase_reset_is_not_monotone :
    let ops : List BarrierOp := [.init 1,.arriveExpectTx 1,.completeTx 1,.tryWaitParity 0 true,
      .arriveExpectTx 1,.completeTx 1,.tryWaitParity 1 true,.inval,.init 1]
    Mbarrier.run none (ops.take 7) = some (some ⟨2,1,1,0,true⟩) ∧
      Mbarrier.run none ops = some (some ⟨0,1,1,0,true⟩) := by decide

open HopperArbitraryHistoryTests
def creditHead : List Tma.Entry := [⟨.source (badFamily.initId 0),.init 1⟩]
def creditTail : List Tma.Entry := [⟨.notification (badFamily.copyBId 0),.completeTx 256⟩]++retrySuccessfulEntries badFamily 0++
  [expectEntry 2,⟨.notification (badFamily.copyAId 2),.completeTx 2048⟩,⟨.notification (badFamily.copyBId 2),.completeTx 256⟩]++
  retrySuccessfulEntries badFamily 2++[⟨.source (badFamily.invalId 0),.inval⟩]
def creditNotice : Tma.Entry := ⟨.notification (badFamily.copyAId 0),.completeTx 2048⟩
def creditNormal : List Tma.Entry := creditHead++expectEntry 0::creditNotice::creditTail
def creditChanged : List Tma.Entry := creditHead++creditNotice::expectEntry 0::creditTail
def creditHistories (loc : Location) : List Tma.Entry := if loc = dataGate 0 then creditChanged else retryHistories badFamily loc

theorem credit_normal_is_constructed : creditNormal = retryResourceHistory badFamily 0 := by decide

theorem early_notice_protocol_valid : Mbarrier.run none (creditChanged.map Tma.Entry.operation) = some none := by decide

theorem early_notice_history_valid : Tma.HistoryValid Tma.localShared badCandidate.view (dataGate 0) creditChanged := by
  have hh : Tma.HistoryValid Tma.localShared badCandidate.view (dataGate 0) creditNormal := by
    rw [credit_normal_is_constructed]
    exact retry_stage_history_valid badFamily (by decide) badSource badDescriptors 0
  have hp : creditNormal.Pairwise Tma.SourceForward := by
    rw [credit_normal_is_constructed]
    exact retry_history_entries_forward badFamily 0
  exact Tma.history_adjacent_swap hh hp (by trivial) ⟨none,early_notice_protocol_valid⟩

theorem early_notice_all_histories_valid (loc : Location) :
    Tma.HistoryValid Tma.localShared badCandidate.view loc (creditHistories loc) := by
  by_cases hz : loc = dataGate 0
  · subst loc
    simp only [creditHistories,ite_true]
    exact early_notice_history_valid
  · rw [creditHistories,ite_eq_right hz]
    exact retry_all_histories_valid badFamily (by decide) badSource badDescriptors loc

theorem early_notice_negative_prefix : Mbarrier.run none ((creditChanged.map Tma.Entry.operation).take 2) =
    some (some ⟨0,1,1,-2048,true⟩) := by decide

theorem early_notice_count_exceeds_arrivals :
    Mbarrier.completionCount 2048 ((creditChanged.map Tma.Entry.operation).take 2) = 1 ∧
      Mbarrier.arrivalCount ((creditChanged.map Tma.Entry.operation).take 2) = 0 := by decide

theorem early_notice_control_rejected : ¬Unified.ControlAcyclic HopperStage.block badCandidate creditHistories := by
  intro hc
  have hp : Mbarrier.run none (((creditHistories (dataGate 0)).map Tma.Entry.operation).take 2) =
      some (some ⟨0,1,1,-2048,true⟩) := by
    simpa only [creditHistories,ite_true] using early_notice_negative_prefix
  have hn := arbitrary_prefix_transactions_nonnegative badFamily (by decide) badSource badDescriptors early_notice_all_histories_valid hc 0 2 _ hp
  norm_num at hn

theorem next_expect_before_peer_wait_rejected : ¬Unified.ControlAcyclic HopperStage.block badCandidate changedHistories := by
  intro hc
  obtain ⟨state,hp,_,hpend,_,_,_⟩ := arbitrary_history_wait_state badFamily (by decide) badSource badDescriptors
    swapped_all_histories_valid hc 0 (by decide) 127
  have hbad : Mbarrier.run none (((changedHistories (dataGate 0)).map Tma.Entry.operation).take
      (actualWaitIndex badFamily changedHistories 0 127)) = some (some ⟨1,1,0,2304,true⟩) := by
    simpa only [actualWaitIndex,show stage 0 = (0 : Stage) from rfl,changedHistories,ite_true] using HopperPrefixAccountingTests.swapped_actual_prefix_state
  have he := Option.some.inj (Option.some.inj (hp.symm.trans hbad))
  rw [he] at hpend
  cases hpend

theorem duplicate_notices_cannot_be_merged :
    let entries : List Tma.Entry := [expectEntry 0,creditNotice,creditNotice]
    ¬entries.Nodup ∧ Mbarrier.completionCount 2048 (entries.map Tma.Entry.operation) = 2 ∧
      Mbarrier.arrivalCount (entries.map Tma.Entry.operation) = 1 := by decide

end
end Ptx.HopperArbitraryObservationTests
