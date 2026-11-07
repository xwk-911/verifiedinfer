import Ptx.Kernels.HopperDoubleBufferRetryArbitraryHistory
import Ptx.Hopper.TmaPrefixAccounting
import Ptx.Hopper.MbarrierTransactionCounts
import Ptx.Hopper.MbarrierResting

/-! Counted phase/transaction equations for arbitrary actual retry histories.
Only inventory multiplicities are transported from the constructed history;
no order equality, readiness or desired completion observation is assumed. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_history_accounting_operations {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot)
    (entry : Tma.Entry) (he : entry ∈ retryResourceHistory family slot) :
    Mbarrier.UnitInitialization entry.operation ∧ Mbarrier.FixedArrival 2304 entry.operation := by
  simp only [retryResourceHistory,List.mem_append,List.mem_singleton] at he
  rcases he with (rfl | he) | rfl
  · simp [Mbarrier.UnitInitialization,Mbarrier.FixedArrival]
  · obtain ⟨phase,_,he⟩ := (retry_phases_entry family slot _ entry).mp he
    have hc := retry_phase_entry_case family slot phase entry he
    cases hc <;> simp [Mbarrier.UnitInitialization,Mbarrier.FixedArrival]
  · simp [Mbarrier.UnitInitialization,Mbarrier.FixedArrival]

theorem retry_history_initialization_count {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot) :
    (((retryResourceHistory family slot).map Tma.Entry.operation).filter Mbarrier.isInitialization).length = 1 := by
  have hnone : ((retryPhases family slot (uses tiles slot)).map Tma.Entry.operation).filter Mbarrier.isInitialization = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro op hop
    obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hop
    obtain ⟨phase,_,he⟩ := (retry_phases_entry family slot _ entry).mp he
    have hc := retry_phase_entry_case family slot phase entry he
    cases hc <;> simp [Mbarrier.isInitialization]
  simp only [retryResourceHistory,List.map_append,List.map_cons,List.map_nil,List.filter_append]
  rw [hnone]
  rfl

theorem arbitrary_history_accounting_inventory {tiles initial candidate} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot) :
    (((histories (dataGate slot)).map Tma.Entry.operation).filter Mbarrier.isInitialization).length = 1 ∧
      (∀ op ∈ (histories (dataGate slot)).map Tma.Entry.operation,
        Mbarrier.UnitInitialization op ∧ Mbarrier.FixedArrival 2304 op) := by
  have hp := (hh (dataGate slot)).exhaustive.trans (retry_history_exhaustive family ht hw hd slot).symm
  constructor
  · exact ((hp.map Tma.Entry.operation).filter Mbarrier.isInitialization).length_eq.trans (retry_history_initialization_count family slot)
  · intro op hop
    obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hop
    exact retry_history_accounting_operations family slot entry (hp.mem_iff.mp he)

theorem arbitrary_history_prefix_accounting {tiles initial candidate} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot cut state)
    (hp : Mbarrier.run none (((histories (dataGate slot)).map Tma.Entry.operation).take cut) = some (some state)) :
    state.expected = 1 ∧ state.pending ≤ 1 ∧
      state.phase+1 = Mbarrier.arrivalCount (((histories (dataGate slot)).map Tma.Entry.operation).take cut)+state.pending ∧
      state.tx = (2304 : Int)*(Mbarrier.arrivalCount (((histories (dataGate slot)).map Tma.Entry.operation).take cut) : Int)-
        (Mbarrier.completedBytes (((histories (dataGate slot)).map Tma.Entry.operation).take cut) : Int) := by
  obtain ⟨hi,hu⟩ := arbitrary_history_accounting_inventory family ht hw hd hh slot
  obtain ⟨he,hpending,hphase,_⟩ := Tma.history_live_prefix_balance (hh _) hi (fun op hop => (hu op hop).1) cut hp
  exact ⟨he,hpending,hphase,Tma.history_fixed_prefix_transactions (hh _) hi (fun op hop => (hu op hop).1)
    (fun op hop => (hu op hop).2) cut hp⟩

theorem arbitrary_history_wait_accounting {tiles initial candidate} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (tile : Nat) (hlt : tile < tiles) (lane : Wgmma.Lane) :
    let entries := histories (dataGate (stage tile))
    let index := (entries.map Tma.Entry.origin).idxOf (.source (family.waitId tile lane))
    ∃ state, Mbarrier.run none ((entries.map Tma.Entry.operation).take index) = some (some state) ∧
      state.expected = 1 ∧ state.pending ≤ 1 ∧
      state.phase+1 = Mbarrier.arrivalCount ((entries.map Tma.Entry.operation).take index)+state.pending ∧
      state.tx = (2304 : Int)*(Mbarrier.arrivalCount ((entries.map Tma.Entry.operation).take index) : Int)-
        (Mbarrier.completedBytes ((entries.map Tma.Entry.operation).take index) : Int) ∧
      0 < state.phase ∧ (expectedParity tile)%2 ≠ state.phase%2 := by
  dsimp only
  have he := Tma.history_entry_at_origin_index (hh _) (retry_wait_resource_at family hw tile hlt lane)
  obtain ⟨state,_,_,hp,hpositive,hparity⟩ := Tma.history_successful_wait_phase (hh _) he
  obtain ⟨hex,hpending,hphase,htx⟩ := arbitrary_history_prefix_accounting family ht hw hd hh (stage tile) _ state hp
  exact ⟨state,hp,hex,hpending,hphase,htx,hpositive,hparity⟩

theorem arbitrary_history_notification_accounting {tiles initial candidate} {histories : Location → List Tma.Entry} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot copy bytes)
    (he : Tma.resourceAt Tma.localShared candidate.view (.notification copy) = some ⟨dataGate slot,.completeTx bytes⟩) :
    let entries := histories (dataGate slot)
    let index := (entries.map Tma.Entry.origin).idxOf (.notification copy)
    ∃ state, Mbarrier.run none ((entries.map Tma.Entry.operation).take index) = some (some state) ∧
      state.expected = 1 ∧ state.pending ≤ 1 ∧
      state.phase+1 = Mbarrier.arrivalCount ((entries.map Tma.Entry.operation).take index)+state.pending ∧
      state.tx = (2304 : Int)*(Mbarrier.arrivalCount ((entries.map Tma.Entry.operation).take index) : Int)-
        (Mbarrier.completedBytes ((entries.map Tma.Entry.operation).take index) : Int) := by
  dsimp only
  obtain ⟨hi,hu⟩ := arbitrary_history_accounting_inventory family ht hw hd hh slot
  have hevent := Tma.history_entry_at_origin_index (hh _) he
  obtain ⟨state,hp,_⟩ := Tma.history_notification_counted_phase (hh _) hi (fun op hop => (hu op hop).1) hevent
  exact ⟨state,hp,arbitrary_history_prefix_accounting family ht hw hd hh slot _ state hp⟩

theorem retry_history_completion_kinds {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot)
    (entry : Tma.Entry) (he : entry ∈ retryResourceHistory family slot) :
    Mbarrier.CompletionKinds 2048 256 entry.operation := by
  simp only [retryResourceHistory,List.mem_append,List.mem_singleton] at he
  rcases he with (rfl | he) | rfl
  · trivial
  · obtain ⟨phase,_,he⟩ := (retry_phases_entry family slot _ entry).mp he
    have hc := retry_phase_entry_case family slot phase entry he
    cases hc <;> simp [Mbarrier.CompletionKinds]
  · trivial

theorem arbitrary_history_completion_kinds {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot) :
    ∀ op ∈ (histories (dataGate slot)).map Tma.Entry.operation, Mbarrier.CompletionKinds 2048 256 op := by
  have hp := (hh (dataGate slot)).exhaustive.trans (retry_history_exhaustive family ht hw hd slot).symm
  intro op hop
  obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hop
  exact retry_history_completion_kinds family slot entry (hp.mem_iff.mp he)

theorem arbitrary_history_prefix_transaction_counts {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot cut state)
    (hp : Mbarrier.run none (((histories (dataGate slot)).map Tma.Entry.operation).take cut) = some (some state)) :
    let ops := ((histories (dataGate slot)).map Tma.Entry.operation).take cut
    state.tx = (2304 : Int)*(Mbarrier.arrivalCount ops : Int)-
      (2048 : Int)*(Mbarrier.completionCount 2048 ops : Int)-(256 : Int)*(Mbarrier.completionCount 256 ops : Int) := by
  dsimp only
  have htx := (arbitrary_history_prefix_accounting family ht hw hd hh slot cut state hp).2.2.2
  have hk := arbitrary_history_completion_kinds family ht hw hd hh slot
  have hc := Mbarrier.completed_bytes_two_kinds (ops := ((histories (dataGate slot)).map Tma.Entry.operation).take cut)
    2048 256 (by decide) (fun op hop => hk op (List.mem_of_mem_take hop))
  rw [hc] at htx
  simp only [Nat.cast_add,Nat.cast_mul] at htx
  omega

theorem arbitrary_history_phase_count_bounds {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot cut state)
    (hp : Mbarrier.run none (((histories (dataGate slot)).map Tma.Entry.operation).take cut) = some (some state)) :
    state.phase ≤ Mbarrier.arrivalCount (((histories (dataGate slot)).map Tma.Entry.operation).take cut) ∧
      Mbarrier.arrivalCount (((histories (dataGate slot)).map Tma.Entry.operation).take cut) ≤ state.phase+1 := by
  obtain ⟨_,hbound,hphase,_⟩ := arbitrary_history_prefix_accounting family ht hw hd hh slot cut state hp
  omega

theorem arbitrary_history_settled_nonpositive {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot cut state)
    (hp : Mbarrier.run none (((histories (dataGate slot)).map Tma.Entry.operation).take cut) = some (some state))
    (hphase : state.phase = Mbarrier.arrivalCount (((histories (dataGate slot)).map Tma.Entry.operation).take cut)) :
    state.tx ≤ 0 := by
  obtain ⟨hex,_,hcount,_⟩ := arbitrary_history_prefix_accounting family ht hw hd hh slot cut state hp
  have hpending : state.pending = state.expected := by omega
  exact Mbarrier.run_resting_nonpositive hp hpending

theorem arbitrary_history_live_prefix_stamp {tiles initial candidate} {histories : Location → List Tma.Entry}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc)) (slot cut state)
    (hp : Mbarrier.run none (((histories (dataGate slot)).map Tma.Entry.operation).take cut) = some (some state)) :
    Tma.stampBefore (histories (dataGate slot)) cut = some ⟨1,state.phase⟩ := by
  obtain ⟨hi,hu⟩ := arbitrary_history_accounting_inventory family ht hw hd hh slot
  exact Tma.history_live_prefix_stamp (hh _) hi (fun op hop => (hu op hop).1) cut hp

end
end Ptx.Kernels.HopperDoubleBuffer
