import Ptx.Kernels.HopperDoubleBufferTmaAgreement
import Ptx.Tests.HopperDoubleBufferResourceOrder

/-! Full local resource-history records, actual-copy agreement, and corrupt
inventory counterexamples. Control and memory admission are not assumed. -/
namespace Ptx.HopperDoubleBufferResourceAdmissionTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

abbrev a := HopperDoubleBufferDataTests.a
abbrev b := HopperDoubleBufferDataTests.b
abbrev history := HopperDoubleBufferResourceTests.history

def missingA := (history 3 0).take 2++(history 3 0).drop 3
def ghostCopy : Tma.CopyId := ⟨(dataInitId 3 0)⟩
def ghostHistory : List Tma.Entry :=
  (history 3 0).take 1++[⟨.notification ghostCopy,.completeTx 0⟩]++(history 3 0).drop 1
def operations (entries : List Tma.Entry) := entries.map Tma.Entry.operation
def originAt (entries : List Tma.Entry) (index : Nat) := (entries[index]?).map Tma.Entry.origin

theorem all_resource_locations_admitted (tiles : Nat) (hb : tiles ≤ 2^28) (loc : Location) :
    Tma.HistoryValid Tma.localShared (dataCompleteCandidate a b tiles).view loc (dataHistories a b tiles loc) :=
  data_all_histories_valid a b tiles hb loc

theorem zero_tile_histories_admitted :
    Tma.HistoryValid Tma.localShared (dataCompleteCandidate a b 0).view (dataGate 0) (history 0 0) ∧
      Tma.HistoryValid Tma.localShared (dataCompleteCandidate a b 0).view (dataGate 1) (history 0 1) :=
  ⟨data_stage_history_valid a b 0 0 (by decide),data_stage_history_valid a b 0 1 (by decide)⟩

theorem three_tile_inventory_lengths :
    (Tma.inventory Tma.localShared (dataCompleteCandidate a b 3).view (dataGate 0)).length = 264 ∧
      (Tma.inventory Tma.localShared (dataCompleteCandidate a b 3).view (dataGate 1)).length = 133 := by
  rw [data_inventory_length a b 3 0 (by decide),data_inventory_length a b 3 1 (by decide)]
  decide

theorem five_tile_inventory_lengths :
    (Tma.inventory Tma.localShared (dataCompleteCandidate a b 5).view (dataGate 0)).length = 395 ∧
      (Tma.inventory Tma.localShared (dataCompleteCandidate a b 5).view (dataGate 1)).length = 264 := by
  rw [data_inventory_length a b 5 0 (by decide),data_inventory_length a b 5 1 (by decide)]
  decide

theorem shared_data_address_has_no_resource :
    Tma.inventory Tma.localShared (dataCompleteCandidate a b 3).view ⟨.shared .zero,16⟩ = [] := by
  apply data_inventory_outside_gates a b 3 (by decide)
  intro slot
  fin_cases slot <;> decide

theorem other_cta_has_no_resource :
    Tma.inventory Tma.localShared (dataCompleteCandidate a b 3).view ⟨.shared ⟨1,0,0⟩,0⟩ = [] := by
  apply data_inventory_outside_gates a b 3 (by decide)
  intro slot
  fin_cases slot <;> decide

theorem missing_a_reduces_inventory : missingA.length = 263 := by decide
theorem missing_a_notice_absent : (⟨.notification (dataCopyAId a b 3 0),.completeTx 2048⟩ : Tma.Entry) ∉ missingA := by decide
theorem missing_a_protocol_rejected : Mbarrier.run none (operations missingA) = none := by decide
theorem missing_a_not_history_valid :
    ¬Tma.HistoryValid Tma.localShared (dataCompleteCandidate a b 3).view (dataGate 0) missingA := by
  intro hv
  have he : Tma.resourceAt Tma.localShared (dataCompleteCandidate a b 3).view (.notification (dataCopyAId a b 3 0)) =
      some ⟨dataGate 0,.completeTx 2048⟩ := data_source_notification_a a b 3 0 (by decide) (by decide)
  exact missing_a_notice_absent (Tma.history_complete hv he)

theorem ghost_protocol_passes : Mbarrier.run none (operations ghostHistory) = some none := by decide
theorem ghost_copy_has_no_source : Tma.copyAt (dataCompleteCandidate a b 3).view ghostCopy = none := by
  have he := Unified.view_barrier_iff.mpr (data_source_init a b 3 0)
  simp only [Tma.copyAt,ghostCopy]
  rw [he]
  rfl
theorem ghost_not_history_valid :
    ¬Tma.HistoryValid Tma.localShared (dataCompleteCandidate a b 3).view (dataGate 0) ghostHistory := by
  intro hv
  have hn := Tma.no_ghost_notification hv ghost_copy_has_no_source (.completeTx 0)
  apply hn
  simp [ghostHistory]

theorem ghost_increases_inventory : ghostHistory.length = 265 := by decide
theorem ghost_location_in_history : originAt ghostHistory 1 = some (.notification ghostCopy) := by decide
theorem first_actual_notice_is_source_copy :
    originAt (history 3 0) 2 = some (.notification (dataCopyAId a b 3 0)) := by decide
theorem reused_actual_notice_is_distinct :
    originAt (history 3 0) 133 = some (.notification (dataCopyAId a b 3 2)) := by decide
theorem all_descriptors_agree (tiles : Nat) (hb : tiles ≤ 2^28) :
    Tma.DescriptorAgreement (dataCompleteCandidate a b tiles).view (dataMaps tiles) := data_descriptor_agreement a b tiles hb
theorem all_payloads_agree (tiles : Nat) (hb : tiles ≤ 2^28) (frame : Location → Symbolic.Byte) :
    Tma.PayloadAgreement (dataCompleteCandidate a b tiles).view (dataRepresentedInitial a b tiles frame) :=
  data_payload_agreement a b tiles frame hb

end
end Ptx.HopperDoubleBufferResourceAdmissionTests
