import Ptx.Kernels.HopperDoubleBufferRetryExactPhases

/-! A missing own notification leaves strictly positive credit. This yields
actual notification-before-wait order from exact wait state and injective
matching, rather than assuming the desired completion observation. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem accounted_notification_at {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (first tile) (ht : tile < tiles) :
    Tma.resourceAt Tma.localShared candidate.view (.notification (accountedCopyId family first tile)) =
      some ⟨dataGate (stage tile),.completeTx (accountedBytes first)⟩ := by
  cases first
  · exact family_notification_b family hw hd tile ht
  · exact family_notification_a family hw hd tile ht

theorem arbitrary_history_accounted_expect_before_notice {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (first tile) (ht : tile < tiles) :
    Tma.Before (histories (dataGate (stage tile))) (.source (family.expectId tile)) (.notification (accountedCopyId family first tile)) := by
  cases first
  · exact arbitrary_history_expect_before_b family hw hd hh hc tile ht
  · exact arbitrary_history_expect_before_a family hw hd hh hc tile ht

theorem arbitrary_prefix_missing_notice_count_lt {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (first tile) (hlt : tile < tiles) (cut : Nat)
    (hp : Tma.Origin.source (family.expectId tile) ∈ ((histories (dataGate (stage tile))).take cut).map Tma.Entry.origin)
    (hn : Tma.Origin.notification (accountedCopyId family first tile) ∉ ((histories (dataGate (stage tile))).take cut).map Tma.Entry.origin) :
    Mbarrier.completionCount (accountedBytes first) (((histories (dataGate (stage tile))).map Tma.Entry.operation).take cut) <
      Mbarrier.arrivalCount (((histories (dataGate (stage tile))).map Tma.Entry.operation).take cut) := by
  rw [← List.map_take,← Tma.completion_entries_count,← Tma.arrival_entries_count]
  have hu := (List.Nodup.of_map Tma.Entry.origin (hh (dataGate (stage tile))).unique).sublist (List.take_sublist cut _)
  have hparent := Tma.prefix_entry_of_origin (origin := .source (family.expectId tile)) (hh _)
    (family_expect_at family hw tile hlt) cut hp
  apply Tma.filter_count_lt_of_missing_parent hu
    (arbitrary_prefix_completion_parent_injective family ht hw hd hh (stage tile) first cut)
    (arbitrary_prefix_completion_parent_present family ht hw hd hh hc (stage tile) first cut)
    ⟨.source (family.expectId tile),.arriveExpectTx 2304⟩ (List.mem_filter.mpr ⟨hparent,rfl⟩)
  intro hm
  obtain ⟨entry,he,heq⟩ := List.mem_map.mp hm
  obtain ⟨hmem,hop⟩ := List.mem_filter.mp he
  obtain ⟨actual,_,_,rfl⟩ := arbitrary_history_completion_entry_case family ht hw hd hh (stage tile) first entry
    (List.mem_of_mem_take hmem) (Tma.completion_entry_operation hop)
  rw [accounted_notice_parent] at heq
  have hactual := family_expect_tile_injective family (Tma.Origin.source.inj (congrArg Tma.Entry.origin heq))
  subst actual
  exact hn (List.mem_map.mpr ⟨_,hmem,rfl⟩)

theorem arbitrary_prefix_missing_notice_transactions_positive {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (first tile) (hlt : tile < tiles) (cut state)
    (hr : Mbarrier.run none (((histories (dataGate (stage tile))).map Tma.Entry.operation).take cut) = some (some state))
    (hp : Tma.Origin.source (family.expectId tile) ∈ ((histories (dataGate (stage tile))).take cut).map Tma.Entry.origin)
    (hn : Tma.Origin.notification (accountedCopyId family first tile) ∉ ((histories (dataGate (stage tile))).take cut).map Tma.Entry.origin) :
    0 < state.tx := by
  have he := arbitrary_history_prefix_transaction_counts family ht hw hd hh (stage tile) cut state hr
  have hstrict := arbitrary_prefix_missing_notice_count_lt family ht hw hd hh hc first tile hlt cut hp hn
  have ha := arbitrary_prefix_completion_count_le_arrivals family ht hw hd hh hc (stage tile) true cut
  have hb := arbitrary_prefix_completion_count_le_arrivals family ht hw hd hh hc (stage tile) false cut
  change Mbarrier.completionCount 2048 _ ≤ Mbarrier.arrivalCount _ at ha
  change Mbarrier.completionCount 256 _ ≤ Mbarrier.arrivalCount _ at hb
  cases first
  · change Mbarrier.completionCount 256 _ < Mbarrier.arrivalCount _ at hstrict
    omega
  · change Mbarrier.completionCount 2048 _ < Mbarrier.arrivalCount _ at hstrict
    omega

theorem arbitrary_history_wait_completion_counts {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (tile : Nat) (hlt : tile < tiles) (lane : Wgmma.Lane) (first : Bool) :
    Mbarrier.completionCount (accountedBytes first) (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
      (actualWaitIndex family histories tile lane)) = tile/2+1 := by
  obtain ⟨state,hr,_,_,htx,hcount,_⟩ := arbitrary_history_wait_state family ht hw hd hh hc tile hlt lane
  have he := arbitrary_history_prefix_transaction_counts family ht hw hd hh (stage tile) _ state hr
  have ha := arbitrary_prefix_completion_count_le_arrivals family ht hw hd hh hc (stage tile) true (actualWaitIndex family histories tile lane)
  have hb := arbitrary_prefix_completion_count_le_arrivals family ht hw hd hh hc (stage tile) false (actualWaitIndex family histories tile lane)
  change Mbarrier.completionCount 2048 _ ≤ Mbarrier.arrivalCount _ at ha
  change Mbarrier.completionCount 256 _ ≤ Mbarrier.arrivalCount _ at hb
  cases first <;> change Mbarrier.completionCount _ _ = tile/2+1 <;> dsimp only [accountedBytes]
  · change Mbarrier.completionCount 256 _ = tile/2+1
    omega
  · change Mbarrier.completionCount 2048 _ = tile/2+1
    omega

theorem arbitrary_history_wait_expect_present {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (tile : Nat) (hlt : tile < tiles) (lane : Wgmma.Lane) :
    Tma.Origin.source (family.expectId tile) ∈ ((histories (dataGate (stage tile))).take
      (actualWaitIndex family histories tile lane)).map Tma.Entry.origin := by
  obtain ⟨_,_,_,_,_,hcount,_⟩ := arbitrary_history_wait_state family ht hw hd hh hc tile hlt lane
  by_contra hn
  have hbound : Mbarrier.arrivalCount (((histories (dataGate (stage tile))).map Tma.Entry.operation).take
      (actualWaitIndex family histories tile lane)) ≤ tile/2 := by
    apply arbitrary_prefix_arrival_count_bound family ht hw hd hh (stage tile) _ (tile/2)
    intro next hnext hs hp
    have hle : next ≤ tile := by
      by_contra hhigher
      have hnot := arbitrary_history_wait_prefix_excludes_later_expect family hw hh hc tile next (by omega) hnext hs.symm lane
        (actualWaitIndex family histories tile lane) (Nat.le_succ _)
      exact hnot hp
    have hne : next ≠ tile := by intro he; subst next; exact hn hp
    have hslot := congrArg Fin.val hs
    dsimp only [stage] at hslot
    omega
  omega

theorem arbitrary_history_notice_before_wait {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (first tile) (hlt : tile < tiles) (lane : Wgmma.Lane) :
    Tma.Before (histories (dataGate (stage tile))) (.notification (accountedCopyId family first tile)) (.source (family.waitId tile lane)) := by
  have hparent := arbitrary_history_wait_expect_present family ht hw hd hh hc tile hlt lane
  have hcount := arbitrary_history_wait_completion_counts family ht hw hd hh hc tile hlt lane first
  obtain ⟨_,_,_,_,_,harrival,_⟩ := arbitrary_history_wait_state family ht hw hd hh hc tile hlt lane
  have hp : Tma.Origin.notification (accountedCopyId family first tile) ∈ ((histories (dataGate (stage tile))).take
      (actualWaitIndex family histories tile lane)).map Tma.Entry.origin := by
    by_contra hn
    have hltcount := arbitrary_prefix_missing_notice_count_lt family ht hw hd hh hc first tile hlt _ hparent hn
    omega
  have hn := Tma.history_complete (hh _) (accounted_notification_at family hw hd first tile hlt)
  have hw := Tma.history_complete (hh _) (retry_wait_resource_at family hw tile hlt lane)
  have hmn : Tma.Origin.notification (accountedCopyId family first tile) ∈ (histories (dataGate (stage tile))).map Tma.Entry.origin :=
    List.mem_map.mpr ⟨_,hn,rfl⟩
  have hmw : Tma.Origin.source (family.waitId tile lane) ∈ (histories (dataGate (stage tile))).map Tma.Entry.origin :=
    List.mem_map.mpr ⟨_,hw,rfl⟩
  rw [List.map_take] at hp
  exact ⟨hmn,hmw,(List.mem_take_iff_idxOf_lt hmn).1 hp⟩

end
end Ptx.Kernels.HopperDoubleBuffer
