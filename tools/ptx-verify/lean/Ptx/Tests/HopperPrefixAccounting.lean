import Ptx.Kernels.HopperDoubleBufferRetryPrefixAccounting
import Ptx.Tests.HopperArbitraryHistory

/-! Operational conservation, lifetime reset and actual arbitrary-history
prefixes. Signed debt and an old-phase successful wait remain admitted by the
protocol; neither is silently ruled out by a counting invariant. -/
namespace Ptx.HopperPrefixAccountingTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem two_arrivers_protocol :
    Mbarrier.run none [.init 2,.arriveExpectTx 3,.arriveExpectTx 5,.completeTx 8,.tryWaitParity 0 true] =
      some (some ⟨1,2,2,0,true⟩) := by decide

theorem two_arrivers_accounting :
    Mbarrier.account [.init 2,.arriveExpectTx 3,.arriveExpectTx 5,.completeTx 8,.tryWaitParity 0 true] = ⟨2,2,8,8⟩ := by decide

theorem zero_byte_arrival_finishes :
    Mbarrier.run none [.init 1,.arriveExpectTx 0,.tryWaitParity 0 true] = some (some ⟨1,1,1,0,true⟩) := by decide

def reinitialized : List BarrierOp := [.init 1,.arriveExpectTx 3,.completeTx 3,.tryWaitParity 0 true,.inval,
  .init 1,.arriveExpectTx 9,.completeTx 9,.tryWaitParity 0 true]

theorem reinitialization_valid : Mbarrier.run none reinitialized = some (some ⟨1,1,1,0,true⟩) := by decide

theorem reinitialization_resets_counters : Mbarrier.account reinitialized = ⟨1,1,9,9⟩ := by decide

theorem reinitialized_global_counts_differ :
    (Mbarrier.account reinitialized).arrivals ≠ Mbarrier.arrivalCount reinitialized := by decide

theorem signed_completion_debt_permitted :
    Mbarrier.run none [.init 1,.completeTx 7] = some (some ⟨0,1,1,-7,true⟩) := by decide

theorem old_phase_wait_with_positive_credit :
    Mbarrier.run none [.init 1,.arriveExpectTx 2304,.completeTx 2048,.completeTx 256,.tryWaitParity 0 true,
      .arriveExpectTx 2304,.tryWaitParity 0 true] = some (some ⟨1,1,0,2304,true⟩) := by decide

theorem wrong_phase_counter_rejected (ops : List BarrierOp)
    (hu : ∀ op ∈ ops, Mbarrier.UnitInitialization op) (ha : (Mbarrier.account ops).arrivals = 2) :
    Mbarrier.run none ops ≠ some (some ⟨4,1,1,0,true⟩) := by
  intro hr
  have hp := (Mbarrier.run_unit_accounting hu hr).2.2.1
  dsimp only at hp
  omega

theorem wrong_transaction_counter_rejected (ops : List BarrierOp) (state : Mbarrier.PhaseState)
    (ha : (Mbarrier.account ops).added = 2304) (hc : (Mbarrier.account ops).completed = 2048) (ht : state.tx ≠ 256) :
    Mbarrier.run none ops ≠ some (some state) := by
  intro hr
  have hx := (Mbarrier.run_accounting hr).2.1
  rw [ha,hc] at hx
  exact ht (by simpa using hx)

theorem two_completion_sizes_counted :
    let ops : List BarrierOp := [.completeTx 256,.tryWaitParity 0 false,.completeTx 2048,.completeTx 256]
    Mbarrier.completedBytes ops = 2560 ∧ Mbarrier.completionCount 2048 ops = 1 ∧ Mbarrier.completionCount 256 ops = 2 := by decide

theorem equal_completion_classes_double_count :
    let ops : List BarrierOp := [.completeTx 256]
    Mbarrier.completedBytes ops ≠ 256*Mbarrier.completionCount 256 ops+256*Mbarrier.completionCount 256 ops := by decide

abbrev family (a b) := HopperArbitraryHistoryTests.family a b
abbrev candidate (a b) := HopperArbitraryHistoryTests.candidate a b
abbrev initial := HopperArbitraryHistoryTests.initial
abbrev source (a b) := retry_data_source a b 3 HopperArbitraryHistoryTests.schedule initial (by decide) (by decide)
abbrev descriptors (a b) := retry_data_descriptors a b 3 HopperArbitraryHistoryTests.schedule (by decide) (by decide)

theorem arbitrary_histories_actual_wait (a b) (histories : Location → List Tma.Entry)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared (candidate a b).view loc (histories loc)) (lane : Wgmma.Lane) :
    let entries := histories (dataGate 0)
    let index := (entries.map Tma.Entry.origin).idxOf (.source ((family a b).waitId 2 lane))
    ∃ state, Mbarrier.run none ((entries.map Tma.Entry.operation).take index) = some (some state) ∧
      state.phase+1 = Mbarrier.arrivalCount ((entries.map Tma.Entry.operation).take index)+state.pending ∧
      state.tx = (2304 : Int)*(Mbarrier.arrivalCount ((entries.map Tma.Entry.operation).take index) : Int)-
        (2048 : Int)*(Mbarrier.completionCount 2048 ((entries.map Tma.Entry.operation).take index) : Int)-
        (256 : Int)*(Mbarrier.completionCount 256 ((entries.map Tma.Entry.operation).take index) : Int) := by
  dsimp only
  obtain ⟨state,hp,_,_,hphase,_⟩ := arbitrary_history_wait_accounting (family a b) (by decide) (source a b) (descriptors a b) hh 2 (by decide) lane
  exact ⟨state,hp,hphase,arbitrary_history_prefix_transaction_counts (family a b) (by decide)
    (source a b) (descriptors a b) hh 0 _ state hp⟩

theorem arbitrary_histories_actual_notice (a b) (histories : Location → List Tma.Entry)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared (candidate a b).view loc (histories loc)) :
    let entries := histories (dataGate 0)
    let index := (entries.map Tma.Entry.origin).idxOf (.notification ((family a b).copyAId 2))
    ∃ state, Mbarrier.run none ((entries.map Tma.Entry.operation).take index) = some (some state) ∧
      state.expected = 1 ∧ state.pending ≤ 1 ∧
      state.phase+1 = Mbarrier.arrivalCount ((entries.map Tma.Entry.operation).take index)+state.pending ∧
      state.tx = (2304 : Int)*(Mbarrier.arrivalCount ((entries.map Tma.Entry.operation).take index) : Int)-
        (Mbarrier.completedBytes ((entries.map Tma.Entry.operation).take index) : Int) :=
  arbitrary_history_notification_accounting (family a b) (by decide) (source a b) (descriptors a b) hh 0 _ _
    (family_notification_a (family a b) (source a b) (descriptors a b) 2 (by decide))

theorem arbitrary_histories_wait_lifetime (a b) (histories : Location → List Tma.Entry)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared (candidate a b).view loc (histories loc)) (lane : Wgmma.Lane) :
    let entries := histories (dataGate 0)
    let index := (entries.map Tma.Entry.origin).idxOf (.source ((family a b).waitId 2 lane))
    ∃ phase, Tma.stampBefore entries index = some ⟨1,phase⟩ := by
  dsimp only
  obtain ⟨state,hp,_⟩ := arbitrary_history_wait_accounting (family a b) (by decide) (source a b) (descriptors a b) hh 2 (by decide) lane
  exact ⟨state.phase,arbitrary_history_live_prefix_stamp (family a b) (by decide) (source a b) (descriptors a b) hh 0 _ state hp⟩

theorem constructed_two_phase_prefix_counts (a b) :
    let ops := ((retryResourceHistory (family a b) 0).map Tma.Entry.operation).take (retryPhaseWaitIndex (family a b) 0 1 127)
    Mbarrier.arrivalCount ops = 2 ∧ (2304 : Int)*(Mbarrier.arrivalCount ops : Int)-(Mbarrier.completedBytes ops : Int) = 0 := by
  dsimp only
  have hp := retry_history_wait_prefix (family a b) 0 1 (by decide) 127
  change Mbarrier.run none (((retryResourceHistory (family a b) 0).map Tma.Entry.operation).take
    (retryPhaseWaitIndex (family a b) 0 1 127)) = some (some (readyState 2)) at hp
  have hprefix : Mbarrier.run none (((retryHistories (family a b) (dataGate 0)).map Tma.Entry.operation).take
      (retryPhaseWaitIndex (family a b) 0 1 127)) = some (some (readyState 2)) := by
    rw [retry_histories_at_gate]
    exact hp
  obtain ⟨_,_,hphase,htx⟩ := arbitrary_history_prefix_accounting (family a b) (by decide) (source a b) (descriptors a b)
    (retry_all_histories_valid (family a b) (by decide) (source a b) (descriptors a b)) 0 _ _ hprefix
  rw [retry_histories_at_gate] at hphase htx
  change 2+1 = _+1 at hphase
  change 0 = _ at htx
  exact ⟨by omega,htx.symm⟩

open HopperArbitraryHistoryTests in
theorem swapped_actual_prefix_state :
    Mbarrier.run none ((changed.map Tma.Entry.operation).take
      ((changed.map Tma.Entry.origin).idxOf (.source (badFamily.waitId 0 127)))) = some (some ⟨1,1,0,2304,true⟩) := by decide

open HopperArbitraryHistoryTests in
theorem swapped_actual_prefix_counts :
    let ops := (changed.map Tma.Entry.operation).take ((changed.map Tma.Entry.origin).idxOf (.source (badFamily.waitId 0 127)))
    Mbarrier.arrivalCount ops = 2 ∧ Mbarrier.completionCount 2048 ops = 1 ∧ Mbarrier.completionCount 256 ops = 1 := by decide

open HopperArbitraryHistoryTests in
theorem swapped_actual_balance_checked :
    let entries := changedHistories (dataGate 0)
    let index := (entries.map Tma.Entry.origin).idxOf (.source (badFamily.waitId 0 127))
    let ops := (entries.map Tma.Entry.operation).take index
    (2304 : Int) = (2304 : Int)*(Mbarrier.arrivalCount ops : Int)-
      (2048 : Int)*(Mbarrier.completionCount 2048 ops : Int)-(256 : Int)*(Mbarrier.completionCount 256 ops : Int) := by
  have hp : Mbarrier.run none (((changedHistories (dataGate 0)).map Tma.Entry.operation).take
      (((changedHistories (dataGate 0)).map Tma.Entry.origin).idxOf (.source (badFamily.waitId 0 127)))) = some (some ⟨1,1,0,2304,true⟩) := by
    simpa only [changedHistories,ite_true] using swapped_actual_prefix_state
  exact arbitrary_history_prefix_transaction_counts badFamily (by decide) badSource badDescriptors swapped_all_histories_valid 0 _ _ hp

end
end Ptx.HopperPrefixAccountingTests
