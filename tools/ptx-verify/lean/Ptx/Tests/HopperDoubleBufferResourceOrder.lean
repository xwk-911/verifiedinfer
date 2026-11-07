import Ptx.Kernels.HopperDoubleBufferResourceSourceOrder
import Ptx.Tests.HopperDoubleBufferResources

/-! Recoverable source identities and ordering, plus corrupted-history checks.
Inventory exhaustion and memory/control admission remain separate obligations. -/
namespace Ptx.HopperDoubleBufferResourceOrderTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

abbrev a := HopperDoubleBufferDataTests.a
abbrev b := HopperDoubleBufferDataTests.b
abbrev history := HopperDoubleBufferResourceTests.history
def rankAt (tiles : Nat) (slot : Stage) (index : Nat) : Option Nat :=
  ((history tiles slot)[index]?).map fun entry => resourcePosition tiles slot entry.origin
def duplicated (tiles : Nat) (slot : Stage) := history tiles slot++(history tiles slot).take 1
def omittedZero := (history 0 0).take 1

theorem initial_ranks : [rankAt 3 0 0,rankAt 3 0 1,rankAt 3 0 2,rankAt 3 0 3,rankAt 3 0 4] =
    [some 0,some 1,some 2,some 3,some 4] := by decide
theorem reused_ranks : [rankAt 3 0 132,rankAt 3 0 133,rankAt 3 0 134,rankAt 3 0 135,rankAt 3 0 262,rankAt 3 0 263] =
    [some 132,some 133,some 134,some 135,some 262,some 263] := by decide
theorem second_slot_ranks : [rankAt 3 1 0,rankAt 3 1 1,rankAt 3 1 4,rankAt 3 1 131,rankAt 3 1 132] =
    [some 0,some 1,some 4,some 131,some 132] := by decide
theorem twice_reused_ranks : rankAt 5 0 264 = some 264 ∧ rankAt 5 0 393 = some 393 ∧ rankAt 5 0 394 = some 394 := by decide
theorem zero_tile_ranks : rankAt 0 0 0 = some 0 ∧ rankAt 0 0 1 = some 1 ∧ rankAt 0 1 1 = some 1 := by decide
theorem source_and_notification_have_distinct_ranks :
    resourcePosition 3 0 (.source ⟨(ctx 3 0).id,41⟩) = 263 ∧
      resourcePosition 5 0 (.notification ⟨⟨(ctx 5 0).id,41⟩⟩) = 265 := by decide
theorem producer_reuse_wait_serial : waitSerial 4 0 = 48 := by decide
theorem peer_reuse_wait_serial : waitSerial 4 127 = 30 := by decide
theorem copy_reuse_serials : copyASerial 4 = 40 ∧ copyBSerial 4 = 41 ∧ expectSerial 4 = 39 := by decide
theorem second_slot_first_serials : expectSerial 1 = 9 ∧ copyASerial 1 = 10 ∧ copyBSerial 1 = 11 := by decide
theorem final_invalidation_serials : invalSerial 5 0 = 61 ∧ invalSerial 5 1 = 62 := by decide
theorem all_use_counts_unique (tiles : Nat) (slot : Stage) : ((history tiles slot).map Tma.Entry.origin).Nodup :=
  data_history_origins_unique a b tiles slot
theorem all_use_counts_source_order (tiles : Nat) (slot : Stage) : Tma.SourceOrder (history tiles slot) :=
  data_history_source_order a b tiles slot
theorem duplicate_initialization_rejected : ¬((duplicated 0 0).map Tma.Entry.origin).Nodup := by decide
theorem reverse_zero_history_rejected : ¬Tma.SourceOrder (history 0 0).reverse := by decide
theorem repeated_source_rejected :
    ¬(([⟨.source (dataInitId 0 0),.init 1⟩,⟨.source (dataInitId 0 0),.inval⟩] : List Tma.Entry).map Tma.Entry.origin).Nodup := by decide
theorem source_order_rejects_inverted_producer_pair :
    ¬Tma.SourceOrder [⟨.source ⟨(ctx 3 0).id,28⟩,.tryWaitParity 1 true⟩,
      ⟨.source ⟨(ctx 3 0).id,19⟩,.arriveExpectTx 2304⟩] := by decide

theorem omitted_invalidation_keeps_local_checks :
    (omittedZero.map Tma.Entry.origin).Nodup ∧ Tma.SourceOrder omittedZero ∧
      Mbarrier.run none (omittedZero.map Tma.Entry.operation) = some (some (readyState 0)) := by decide

theorem omitted_invalidation_not_history_valid :
    ¬Tma.HistoryValid Tma.localShared (dataCompleteCandidate a b 0).view (dataGate 0) omittedZero := by
  intro hv
  have hm := Tma.history_complete hv (data_resource_inval a b 0 0)
  have hn : (⟨.source (dataInvalId a b 0 0),.inval⟩ : Tma.Entry) ∉ omittedZero := by decide
  exact hn hm

end
end Ptx.HopperDoubleBufferResourceOrderTests
