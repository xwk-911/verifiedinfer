import Ptx.Kernels.HopperDoubleBufferRetryArbitraryHistory
import Ptx.Kernels.HopperDoubleBufferRetryDataExecution
import Ptx.Hopper.TmaHistorySwap
import Ptx.Tests.HopperRetryPrefetch

/-! Arbitrary-history bounds and an actual three-tile counterexample:
protocol, source order and exhaustive inventory survive a peer-wait/next-expect
swap, but CTA control rejects it. Protocol success is not phase attribution. -/
namespace Ptx.HopperArbitraryHistoryTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev schedule := HopperRetryPrefetchTests.schedule
abbrev family (a b) := retryDataFamily a b 3 schedule
abbrev candidate (a b) := retryDataCandidate a b 3 schedule
abbrev initial : Location → Symbolic.Byte := fun _ => .bits (byte 0)

theorem arbitrary_histories_phase_bounds (a b) (histories : Location → List Tma.Entry)
    (ht : Unified.TmaComponents code (completeLaunch 3 initial) (candidate a b) Tma.localShared (dataMaps 3) histories)
    (hc : Unified.ControlAdmitted HopperStage.block (candidate a b) histories) :
    (∀ tile : Fin 3, Tma.Before (histories (dataGate (stage tile))) (.source ((family a b).expectId tile)) (.notification ((family a b).copyAId tile)) ∧
      Tma.Before (histories (dataGate (stage tile))) (.source ((family a b).expectId tile)) (.notification ((family a b).copyBId tile))) ∧
    (∀ lane, Tma.Before (histories (dataGate 0)) (.source ((family a b).waitId 0 lane)) (.source ((family a b).expectId 2))) := by
  obtain ⟨hcopy,hreuse⟩ := admitted_history_phase_bounds (family a b) ht hc
  exact ⟨fun tile => hcopy tile tile.isLt,fun lane => hreuse 0 2 (by decide) (by decide) (by decide) lane⟩

theorem actual_all_lane_reuse_bounds (a b) (lane : Wgmma.Lane) :
    Tma.Before (retryHistories (family a b) (dataGate 0)) (.source ((family a b).waitId 0 lane)) (.source ((family a b).expectId 2)) :=
  arbitrary_history_wait_before_later_expect (family a b) (retry_data_source a b 3 schedule initial (by decide) (by decide))
    (retry_all_histories_valid (family a b) (by decide) (retry_data_source a b 3 schedule initial (by decide) (by decide))
      (retry_data_descriptors a b 3 schedule (by decide) (by decide)))
    (retry_unified_control_acyclic (family a b) (by decide) (by decide) (retry_data_source a b 3 schedule initial (by decide) (by decide)))
    0 2 (by decide) (by decide) (by decide) lane

theorem actual_notification_prefix (a b) (tile : Fin 3) (cut : Nat)
    (hp : Tma.Origin.notification ((family a b).copyAId tile) ∈ ((retryHistories (family a b) (dataGate (stage tile))).take cut).map Tma.Entry.origin) :
    Tma.Origin.source ((family a b).expectId tile) ∈ ((retryHistories (family a b) (dataGate (stage tile))).take cut).map Tma.Entry.origin :=
  arbitrary_history_notification_a_prefix (family a b) (retry_data_source a b 3 schedule initial (by decide) (by decide))
    (retry_data_descriptors a b 3 schedule (by decide) (by decide))
    (retry_all_histories_valid (family a b) (by decide) (retry_data_source a b 3 schedule initial (by decide) (by decide))
      (retry_data_descriptors a b 3 schedule (by decide) (by decide)))
    (retry_unified_control_acyclic (family a b) (by decide) (by decide) (retry_data_source a b 3 schedule initial (by decide) (by decide))) tile tile.isLt cut hp

theorem old_phase_true_wait_can_follow_next_expect :
    Mbarrier.run (some ⟨1,1,1,0,true⟩) [.arriveExpectTx 2304,.tryWaitParity 0 true] = some (some ⟨1,1,0,2304,true⟩) := by decide

abbrev noRetries : Wgmma.Lane → Nat → Nat := fun _ _ => 0
abbrev badFamily := retryDataFamily (fun _ _ => 1) (fun _ _ => 2) 3 noRetries
abbrev badCandidate := retryDataCandidate (fun _ _ => 1) (fun _ _ => 2) 3 noRetries
abbrev badSource := retry_data_source (fun _ _ => 1) (fun _ _ => 2) 3 noRetries initial (by decide) (by decide)
abbrev badDescriptors := retry_data_descriptors (fun _ _ => 1) (fun _ _ => 2) 3 noRetries (by decide) (by decide)

def waitEntry (tile : Nat) (lane : Wgmma.Lane) : Tma.Entry := ⟨.source (badFamily.waitId tile lane),.tryWaitParity (expectedParity tile) true⟩
def expectEntry (tile : Nat) : Tma.Entry := ⟨.source (badFamily.expectId tile),.arriveExpectTx 2304⟩
def beforeEntries : List Tma.Entry :=
  [⟨.source (badFamily.initId 0),.init 1⟩,expectEntry 0,
   ⟨.notification (badFamily.copyAId 0),.completeTx 2048⟩,⟨.notification (badFamily.copyBId 0),.completeTx 256⟩]++
    List.ofFn (fun lane : Fin 127 => waitEntry 0 ⟨lane.val,by omega⟩)
def afterEntries : List Tma.Entry :=
  [⟨.notification (badFamily.copyAId 2),.completeTx 2048⟩,⟨.notification (badFamily.copyBId 2),.completeTx 256⟩]++
    retrySuccessfulEntries badFamily 2++[⟨.source (badFamily.invalId 0),.inval⟩]
def normal : List Tma.Entry := beforeEntries++waitEntry 0 127::expectEntry 2::afterEntries
def changed : List Tma.Entry := beforeEntries++expectEntry 2::waitEntry 0 127::afterEntries
def changedHistories (loc : Location) : List Tma.Entry := if loc = dataGate 0 then changed else retryHistories badFamily loc

theorem normal_is_constructed : normal = retryResourceHistory badFamily 0 := by decide

theorem swapped_history_protocol : Mbarrier.run none (changed.map Tma.Entry.operation) = some none := by decide

theorem swapped_source_forward : Tma.SourceForward (expectEntry 2) (waitEntry 0 127) := by
  change (ctx 3 0).id = (ctx 3 127).id → _
  have hn : (ctx 3 0).id ≠ (ctx 3 127).id := by decide
  intro he
  exact (hn he).elim

theorem swapped_history_valid : Tma.HistoryValid Tma.localShared badCandidate.view (dataGate 0) changed := by
  have hh : Tma.HistoryValid Tma.localShared badCandidate.view (dataGate 0) normal := by
    rw [normal_is_constructed]
    exact retry_stage_history_valid badFamily (by decide) badSource badDescriptors 0
  have hp : normal.Pairwise Tma.SourceForward := by rw [normal_is_constructed]; exact retry_history_entries_forward badFamily 0
  exact Tma.history_adjacent_swap hh hp swapped_source_forward ⟨none,swapped_history_protocol⟩

theorem swapped_all_histories_valid (loc : Location) :
    Tma.HistoryValid Tma.localShared badCandidate.view loc (changedHistories loc) := by
  by_cases hz : loc = dataGate 0
  · subst loc
    simp only [changedHistories,ite_true]
    exact swapped_history_valid
  · rw [changedHistories,ite_eq_right hz]
    exact retry_all_histories_valid badFamily (by decide) badSource badDescriptors loc

theorem swapped_reverse_order : Tma.Before changed (.source (badFamily.expectId 2)) (.source (badFamily.waitId 0 127)) := by decide

theorem swapped_control_rejected : ¬Unified.ControlAdmitted HopperStage.block badCandidate changedHistories := by
  intro hc
  have hforward := arbitrary_history_wait_before_later_expect badFamily badSource swapped_all_histories_valid hc.2 0 2 (by decide) (by decide) (by decide) 127
  have hreverse : Tma.Before (changedHistories (dataGate 0)) (.source (badFamily.expectId 2)) (.source (badFamily.waitId 0 127)) := by
    simpa only [changedHistories,ite_true] using swapped_reverse_order
  exact Nat.lt_asymm hforward.2.2 hreverse.2.2

theorem swapped_history_is_noncanonical : changed ≠ retryResourceHistory badFamily 0 := by decide

end
end Ptx.HopperArbitraryHistoryTests
