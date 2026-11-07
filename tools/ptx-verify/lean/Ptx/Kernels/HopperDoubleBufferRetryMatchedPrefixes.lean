import Ptx.Kernels.HopperDoubleBufferRetryPrefixAccounting
import Ptx.Hopper.TmaMatchedCounts

/-! Actual completion-to-expect injections for every admitted history prefix.
Source metadata identifies parents; actual control paths establish prefix
presence. No canonical history order or nonnegative-credit premise is used. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def accountedCopyId {tiles candidate} (family : ReplySourceFamily tiles candidate) (first : Bool) (tile : Nat) : Tma.CopyId :=
  if first then family.copyAId tile else family.copyBId tile
def accountedBytes (first : Bool) : Nat := if first then 2048 else 256
def accountedOffset (first : Bool) : Nat := if first then 1 else 2

theorem accounted_notice_parent {tiles candidate} (family : ReplySourceFamily tiles candidate) (first : Bool) (tile : Nat) :
    Tma.noticeParent (accountedOffset first) 2304 ⟨.notification (accountedCopyId family first tile),.completeTx (accountedBytes first)⟩ =
      ⟨.source (family.expectId tile),.arriveExpectTx 2304⟩ := by
  cases first <;> cases tile <;>
    simp [Tma.noticeParent,accountedCopyId,accountedBytes,accountedOffset,ReplySourceFamily.copyAId,ReplySourceFamily.copyBId,
      ReplySourceFamily.expectId,replyCopyAId,replyCopyBId,replyExpectId,replyPrefetchId]

theorem arbitrary_history_completion_entry_case {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot first entry)
    (he : entry ∈ histories (dataGate slot)) (hop : entry.operation = .completeTx (accountedBytes first)) :
    ∃ tile, tile < tiles ∧ stage tile = slot ∧
      entry = ⟨.notification (accountedCopyId family first tile),.completeTx (accountedBytes first)⟩ := by
  have hp := (hh (dataGate slot)).exhaustive.trans (retry_history_exhaustive family ht hw hd slot).symm
  have hm := hp.mem_iff.mp he
  simp only [retryResourceHistory,List.mem_append,List.mem_singleton] at hm
  rcases hm with (rfl | hm) | rfl
  · cases first <;> cases hop
  · obtain ⟨phase,hphase,hm⟩ := (retry_phases_entry family slot _ entry).mp hm
    have hc := retry_phase_entry_case family slot phase entry hm
    refine ⟨stageTile slot phase,(stage_tile_in_range tiles slot phase).mpr hphase,stage_tile_slot slot phase,?_⟩
    cases first <;> cases hc <;> simp_all [accountedCopyId,accountedBytes]
  · cases first <;> cases hop

theorem arbitrary_history_accounted_notice_prefix {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (first tile) (ht : tile < tiles) (cut : Nat)
    (hp : Tma.Origin.notification (accountedCopyId family first tile) ∈ ((histories (dataGate (stage tile))).take cut).map Tma.Entry.origin) :
    Tma.Origin.source (family.expectId tile) ∈ ((histories (dataGate (stage tile))).take cut).map Tma.Entry.origin := by
  cases first
  · exact arbitrary_history_notification_b_prefix family hw hd hh hc tile ht cut hp
  · exact arbitrary_history_notification_a_prefix family hw hd hh hc tile ht cut hp

theorem arbitrary_prefix_completion_parent_injective {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot first cut) :
    ∀ x ∈ ((histories (dataGate slot)).take cut).filter (Tma.isCompletionEntry (accountedBytes first)),
      ∀ y ∈ ((histories (dataGate slot)).take cut).filter (Tma.isCompletionEntry (accountedBytes first)),
      Tma.noticeParent (accountedOffset first) 2304 x = Tma.noticeParent (accountedOffset first) 2304 y → x = y := by
  intro x hx y hy heq
  obtain ⟨hx,hxop⟩ := List.mem_filter.mp hx
  obtain ⟨hy,hyop⟩ := List.mem_filter.mp hy
  obtain ⟨left,_,_,rfl⟩ := arbitrary_history_completion_entry_case family ht hw hd hh slot first x (List.mem_of_mem_take hx) (Tma.completion_entry_operation hxop)
  obtain ⟨right,_,_,rfl⟩ := arbitrary_history_completion_entry_case family ht hw hd hh slot first y (List.mem_of_mem_take hy) (Tma.completion_entry_operation hyop)
  rw [accounted_notice_parent,accounted_notice_parent] at heq
  have hi := Tma.Origin.source.inj (congrArg Tma.Entry.origin heq)
  have htile := family_expect_tile_injective family hi
  subst right
  rfl

theorem arbitrary_prefix_completion_parent_present {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (slot first cut) :
    ∀ entry ∈ ((histories (dataGate slot)).take cut).filter (Tma.isCompletionEntry (accountedBytes first)),
      Tma.noticeParent (accountedOffset first) 2304 entry ∈ ((histories (dataGate slot)).take cut).filter Tma.isArrivalEntry := by
  intro entry he
  obtain ⟨hmem,hop⟩ := List.mem_filter.mp he
  obtain ⟨tile,htile,hslot,rfl⟩ := arbitrary_history_completion_entry_case family ht hw hd hh slot first entry
    (List.mem_of_mem_take hmem) (Tma.completion_entry_operation hop)
  rw [accounted_notice_parent]
  have hnotice : Tma.Origin.notification (accountedCopyId family first tile) ∈
      ((histories (dataGate (stage tile))).take cut).map Tma.Entry.origin := by
    rw [hslot]
    exact List.mem_map.mpr ⟨_,hmem,rfl⟩
  have hparent := arbitrary_history_accounted_notice_prefix family hw hd hh hc first tile htile cut hnotice
  have he := Tma.prefix_entry_of_origin (origin := .source (family.expectId tile))
    (hh (dataGate (stage tile))) (family_expect_at family hw tile htile) cut hparent
  rw [hslot] at he
  exact List.mem_filter.mpr ⟨he,rfl⟩

theorem arbitrary_prefix_completion_count_le_arrivals {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (slot first cut) :
    Mbarrier.completionCount (accountedBytes first) (((histories (dataGate slot)).map Tma.Entry.operation).take cut) ≤
      Mbarrier.arrivalCount (((histories (dataGate slot)).map Tma.Entry.operation).take cut) := by
  rw [← List.map_take]
  have hu := (List.Nodup.of_map Tma.Entry.origin (hh (dataGate slot)).unique).sublist (List.take_sublist cut _)
  exact Tma.completion_count_le_arrivals (accountedBytes first) (Tma.noticeParent (accountedOffset first) 2304) hu
    (arbitrary_prefix_completion_parent_injective family ht hw hd hh slot first cut)
    (arbitrary_prefix_completion_parent_present family ht hw hd hh hc slot first cut)

theorem arbitrary_prefix_transactions_nonnegative {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (slot cut state)
    (hp : Mbarrier.run none (((histories (dataGate slot)).map Tma.Entry.operation).take cut) = some (some state)) :
    0 ≤ state.tx := by
  have he := arbitrary_history_prefix_transaction_counts family ht hw hd hh slot cut state hp
  have ha := arbitrary_prefix_completion_count_le_arrivals family ht hw hd hh hc slot true cut
  have hb := arbitrary_prefix_completion_count_le_arrivals family ht hw hd hh hc slot false cut
  change Mbarrier.completionCount 2048 _ ≤ Mbarrier.arrivalCount _ at ha
  change Mbarrier.completionCount 256 _ ≤ Mbarrier.arrivalCount _ at hb
  omega

theorem arbitrary_prefix_settled_transactions_zero {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (slot cut state)
    (hp : Mbarrier.run none (((histories (dataGate slot)).map Tma.Entry.operation).take cut) = some (some state))
    (hphase : state.phase = Mbarrier.arrivalCount (((histories (dataGate slot)).map Tma.Entry.operation).take cut)) :
    state.tx = 0 := by
  have hlo := arbitrary_prefix_transactions_nonnegative family ht hw hd hh hc slot cut state hp
  have hhi := arbitrary_history_settled_nonpositive family ht hw hd hh slot cut state hp hphase
  omega

end
end Ptx.Kernels.HopperDoubleBuffer
