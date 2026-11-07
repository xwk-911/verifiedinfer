import Ptx.Kernels.HopperDoubleBufferRetryMatchedNotices

/-! Actual copy completion observations in arbitrary admitted histories.
Notice/wait indices, lifetime stamps and exact phases are derived separately.
This removes the constructed-history restriction for completion observations,
not yet for the full input/read/observer refinement theorem. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem arbitrary_history_notice_exact_phase {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (first tile) (hlt : tile < tiles) :
    ∃ state, Mbarrier.run none (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
      (actualNoticeIndex family histories first tile)) = some (some state) ∧
      state.phase = tile/2 ∧ state.pending = 0 ∧ 0 < state.tx ∧
      Tma.stampBefore (histories (dataGate (stage tile))) (actualNoticeIndex family histories first tile) = some ⟨1,tile/2⟩ := by
  obtain ⟨state,hr,hex,hbound,hbalance,_⟩ := arbitrary_history_notification_accounting family ht hw hd hh (stage tile)
    (accountedCopyId family first tile) (accountedBytes first) (accounted_notification_at family hw hd first tile hlt)
  change Mbarrier.run none (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
    (actualNoticeIndex family histories first tile)) = some (some state) at hr
  change state.phase+1 = Mbarrier.arrivalCount (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
    (actualNoticeIndex family histories first tile))+state.pending at hbalance
  have hexpect := arbitrary_history_accounted_expect_before_notice family hw hd hh hc first tile hlt
  have hparent := Tma.before_left_in_right_prefix hexpect
  have hmissing := Tma.origin_not_in_own_prefix hexpect.2.1
  have hcredit := arbitrary_prefix_missing_notice_transactions_positive family ht hw hd hh hc first tile hlt _ state hr hparent hmissing
  have hrest := Mbarrier.run_resting_nonpositive hr
  have hpending : state.pending = 0 := by
    by_contra hn
    have heq : state.pending = state.expected := by omega
    have hnonpos := hrest heq
    omega
  obtain ⟨_,_,_,_,_,hwaitCount,_⟩ := arbitrary_history_wait_state family ht hw hd hh hc tile hlt 0
  have horder := arbitrary_history_notice_before_wait family ht hw hd hh hc first tile hlt 0
  have hcountle : Mbarrier.arrivalCount (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
      (actualNoticeIndex family histories first tile)) ≤ Mbarrier.arrivalCount (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
      (actualWaitIndex family histories tile 0)) :=
    Mbarrier.arrival_count_take_mono _ (Nat.le_of_lt horder.2.2)
  have hupper : state.phase ≤ tile/2 := by omega
  have hlower : tile/2 ≤ state.phase := by
    cases hround : tile/2 with
    | zero => omega
    | succ previous =>
      let oldTile := stageTile (stage tile) previous
      have hold : oldTile < tile := by
        have hid := stage_tile_index tile
        rw [hround] at hid
        dsimp only [oldTile,stageTile] at hid ⊢
        omega
      have hslot : stage oldTile = stage tile := stage_tile_slot _ _
      have hdiv : oldTile/2 = previous := by
        have := (stage tile).isLt
        dsimp only [oldTile,stageTile]
        omega
      obtain ⟨before,hbefore,hbeforePhase,_⟩ := arbitrary_history_wait_state family ht hw hd hh hc oldTile (by omega) 0
      rw [hdiv] at hbeforePhase
      have hprior := arbitrary_history_wait_before_later_expect family hw hh hc oldTile tile hold hlt hslot 0
      rw [hslot] at hprior hbefore
      have hindex : actualWaitIndex family histories oldTile 0 ≤ actualNoticeIndex family histories first tile := by
        simpa only [actualWaitIndex,actualNoticeIndex,hslot] using Nat.le_of_lt (hprior.2.2.trans hexpect.2.2)
      have hm := arbitrary_history_prefix_phase_mono family ht hw hd hh (stage tile) _ _ before state hindex hbefore hr
      omega
  have hphase := Nat.le_antisymm hupper hlower
  have hs := arbitrary_history_live_prefix_stamp family ht hw hd hh (stage tile) _ state hr
  rw [hphase] at hs
  exact ⟨state,hr,hphase,hpending,hcredit,hs⟩

theorem arbitrary_history_observe {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (first tile) (hlt : tile < tiles) (lane : Wgmma.Lane) :
    Tma.observation (histories (dataGate (stage tile))) (actualNoticeIndex family histories first tile)
      (actualWaitIndex family histories tile lane) = some (accountedCopyId family first tile,family.waitId tile lane) := by
  obtain ⟨_,_,_,_,_,hnotice⟩ := arbitrary_history_notice_exact_phase family ht hw hd hh hc first tile hlt
  obtain ⟨_,_,_,_,_,_,hwait⟩ := arbitrary_history_wait_state family ht hw hd hh hc tile hlt lane
  have hn := Tma.history_entry_at_origin_index (origin := .notification (accountedCopyId family first tile))
    (hh _) (accounted_notification_at family hw hd first tile hlt)
  have hwevent := Tma.history_entry_at_origin_index (origin := .source (family.waitId tile lane)) (hh _) (retry_wait_resource_at family hw tile hlt lane)
  have horder := arbitrary_history_notice_before_wait family ht hw hd hh hc first tile hlt lane
  unfold Tma.observation
  change _ = some (accountedCopyId family first tile,family.waitId tile lane)
  rw [show (histories (dataGate (stage tile)))[actualNoticeIndex family histories first tile]? =
      some ⟨.notification (accountedCopyId family first tile),.completeTx (accountedBytes first)⟩ from hn,
    show (histories (dataGate (stage tile)))[actualWaitIndex family histories tile lane]? =
      some ⟨.source (family.waitId tile lane),.tryWaitParity (expectedParity tile) true⟩ from hwevent]
  simp only [bind,Option.bind,Tma.noticeCopy,Tma.waitEvent]
  rw [hnotice,hwait]
  dsimp only
  rw [ite_eq_left ⟨horder.2.2,rfl,rfl⟩]

theorem arbitrary_history_completion_observed {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (first tile) (hlt : tile < tiles) (lane : Wgmma.Lane) :
    Access.CompletionObserved Tma.localShared candidate.view histories dataCluster (accountedCopyId family first tile) (family.waitId tile lane) := by
  refine ⟨?_,dataGate (stage tile),actualNoticeIndex family histories first tile,actualWaitIndex family histories tile lane,
    rfl,hh _,arbitrary_history_observe family ht hw hd hh hc first tile hlt lane⟩
  · cases first <;> cases tile <;> rfl

theorem arbitrary_histories_completion_observations {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) histories)
    (hc : Unified.ControlAdmitted HopperStage.block candidate histories) :
    ∀ tile, tile < tiles → ∀ lane,
      Access.CompletionObserved Tma.localShared candidate.view histories dataCluster (family.copyAId tile) (family.waitId tile lane) ∧
      Access.CompletionObserved Tma.localShared candidate.view histories dataCluster (family.copyBId tile) (family.waitId tile lane) := by
  intro tile htile lane
  exact ⟨arbitrary_history_completion_observed family ht htma.source htma.descriptors htma.histories_valid hc.2 true tile htile lane,
    arbitrary_history_completion_observed family ht htma.source htma.descriptors htma.histories_valid hc.2 false tile htile lane⟩

theorem completed_candidate_arbitrary_observations {tiles initial candidate} {histories : Location → List Tma.Entry}
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) histories)
    (hcomplete : Unified.Complete candidate) (hc : Unified.ControlAdmitted HopperStage.block candidate histories) :
    ∃ family : ReplySourceFamily tiles candidate, ∀ tile, tile < tiles → ∀ lane,
      Access.CompletionObserved Tma.localShared candidate.view histories dataCluster (family.copyAId tile) (family.waitId tile lane) ∧
      Access.CompletionObserved Tma.localShared candidate.view histories dataCluster (family.copyBId tile) (family.waitId tile lane) := by
  obtain ⟨family⟩ := completed_candidate_reply_family ht hb htma.source hcomplete
  exact ⟨family,arbitrary_histories_completion_observations family ht htma hc⟩

theorem arbitrary_history_wrong_tile_not_observed {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (first old current)
    (ho : old < tiles) (hcurrent : current < tiles) (hs : stage old = stage current) (hne : old ≠ current) (lane : Wgmma.Lane) :
    Tma.observation (histories (dataGate (stage current))) (actualNoticeIndex family histories first old)
      (actualWaitIndex family histories current lane) = none := by
  obtain ⟨_,_,_,_,_,hnotice⟩ := arbitrary_history_notice_exact_phase family ht hw hd hh hc first old ho
  obtain ⟨_,_,_,_,_,_,hwait⟩ := arbitrary_history_wait_state family ht hw hd hh hc current hcurrent lane
  rw [hs] at hnotice
  apply Tma.observation_no_phase_match hnotice hwait
  have hslot := congrArg Fin.val hs
  dsimp only [stage] at hslot
  intro he
  change old/2+1 = current/2+1 at he
  exact hne (by omega)

end
end Ptx.Kernels.HopperDoubleBuffer
