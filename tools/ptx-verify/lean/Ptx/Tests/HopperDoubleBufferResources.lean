import Ptx.Kernels.HopperDoubleBufferResourceObservations
import Ptx.Tests.HopperDoubleBufferIndices

/-! Concrete source-ID, protocol-prefix and phase-observation checks. The
constructed histories are not yet claimed to satisfy all HistoryValid fields. -/
namespace Ptx.HopperDoubleBufferResourceTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

abbrev a := HopperDoubleBufferDataTests.a
abbrev b := HopperDoubleBufferDataTests.b
def history (tiles : Nat) (slot : Stage) := dataResourceHistory a b tiles slot
def observed (tiles : Nat) (slot : Stage) (notice waiting : Nat) : Option (Nat × Nat) :=
  (Tma.observation (history tiles slot) notice waiting).map fun pair => (pair.1.issue.serial,pair.2.serial)
def stamp (tiles : Nat) (slot : Stage) (index : Nat) := Tma.stampBefore (history tiles slot) index
def protocol (tiles : Nat) (slot : Stage) := Mbarrier.run none ((history tiles slot).map Tma.Entry.operation)
def originAt (tiles : Nat) (slot : Stage) (index : Nat) := ((history tiles slot)[index]?).map Tma.Entry.origin

theorem history_lengths : (history 3 0).length = 264 ∧ (history 3 1).length = 133 ∧ (history 5 0).length = 395 := by decide
theorem zero_history_lengths : (history 0 0).length = 2 ∧ (history 0 1).length = 2 := by decide
theorem all_phases_finish : protocol 5 0 = some none ∧ protocol 5 1 = some none := by decide
theorem zero_phases_finish : protocol 0 0 = some none ∧ protocol 0 1 = some none := by decide
theorem initial_a_observed : observed 3 0 2 4 = some (6,8) := by decide
theorem initial_b_observed_by_last_peer : observed 3 0 3 131 = some (7,2) := by decide
theorem second_slot_a_observed : observed 3 1 2 4 = some (10,18) := by decide
theorem reused_a_observed : observed 3 0 133 135 = some (20,28) := by decide
theorem reused_b_observed_by_last_peer : observed 3 0 134 262 = some (21,16) := by decide
theorem twice_reused_a_observed : observed 5 0 264 393 = some (40,30) := by decide
theorem stale_a_not_observed : observed 3 0 2 135 = none := by decide
theorem stale_b_not_observed : observed 3 0 3 262 = none := by decide
theorem parity_wrap_does_not_revive_a : observed 5 0 2 266 = none := by decide
theorem parity_wrap_does_not_revive_b : observed 5 0 3 393 = none := by decide
theorem future_a_not_observed : observed 3 0 133 4 = none := by decide
theorem source_expect_is_not_notice : observed 3 0 1 4 = none := by decide
theorem arrival_is_not_successful_wait : observed 3 0 2 1 = none := by decide
theorem notices_before_completion_have_old_phase : stamp 3 0 2 = some ⟨1,0⟩ ∧ stamp 3 0 3 = some ⟨1,0⟩ := by decide
theorem wait_advances_phase : stamp 3 0 4 = some ⟨1,1⟩ ∧ stamp 3 0 131 = some ⟨1,1⟩ := by decide
theorem reused_wait_advances_phase : stamp 3 0 133 = some ⟨1,1⟩ ∧ stamp 3 0 135 = some ⟨1,2⟩ := by decide
theorem parity_wrap_keeps_lifetime : stamp 5 0 264 = some ⟨1,2⟩ ∧ stamp 5 0 393 = some ⟨1,3⟩ := by decide
theorem invalidation_is_actual_source :
    originAt 3 0 263 = some (.source ⟨(ctx 3 0).id,41⟩) ∧
      originAt 3 1 132 = some (.source ⟨(ctx 3 0).id,42⟩) := by decide
theorem init_source_ids : (dataInitId 3 0).serial = 0 ∧ (dataInitId 3 1).serial = 1 := by decide
theorem inval_source_ids : (dataInvalId a b 3 0).serial = 41 ∧ (dataInvalId a b 3 1).serial = 42 := by decide
theorem last_peer_wait_is_actual_source :
    originAt 3 0 262 = some (.source ⟨(ctx 3 127).id,16⟩) := by decide

end
end Ptx.HopperDoubleBufferResourceTests
