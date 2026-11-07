import Ptx.Iris.ByteContentsFootprint
import Ptx.Tests.ByteContents

/-! Real RMW value updates with footprint ownership, including an actually
allocated disjoint fractional byte frame. No full-heap value update is used.
-/
namespace Ptx.ByteContentsFootprintTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
open Ptx.ByteRetirementTests Ptx.ByteAcquisitionTests Ptx.ByteExecutionTests Ptx.ByteContentsTests
noncomputable section

def values : Location → Option Symbolic.Byte := fun _ => some (.bits (byte 0))

theorem initial_pool_has_actual_free_payloads : ByteContentsHeap.Free initialState rmwDemands values := by
  intro demand hm
  exact ByteContents.initialCells_member (List.mem_map.mpr ⟨demand,hm,rfl⟩)

theorem generic_grants_are_the_actual_four_claims :
    ByteContentsHeap.granted initialState rmwNode rmwDemands values = acquiredState 4 := by rfl

theorem actual_acquired_payloads_match_local_rule : ByteContentsHeap.Matches (acquiredState 4) rmwNode rmwDemands values := by
  intro demand hm
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hm
  exact acquired_values_are_still_initial index

theorem same_real_actions_are_used : ByteContentsHeap.cycleActions memoryNode rmwDemands = actions := by rfl

theorem local_finish_frames_arbitrary_resources [ByteContentsHeap.GS] (frame : IProp ByteContentsHeap.GF) :
    ByteContentsHeap.control (acquiredState 4) ∗ ByteContentsHeap.heldPoints rmwNode rmwDemands values ∗ frame ⊢
      WP (ByteContentsHeap.script ctx [.finish memoryNode rmwDemands])
      {{ result, ⌜result = .ok finalState⌝ ∗ ByteContentsHeap.control finalState ∗
        ByteContentsHeap.freePoints rmwDemands (ByteContentsHeap.returnedValues rmwCandidate memoryNode values) ∗ frame }} :=
  ByteContentsHeap.finish_local_wp ctx _ _ memoryNode rmwDemands values frame finish_checks_permissions_and_values actual_acquired_payloads_match_local_rule

theorem local_cycle_starts_from_available_payloads [ByteContentsHeap.GS] (frame : IProp ByteContentsHeap.GF) :
    ByteContentsHeap.control initialState ∗ ByteContentsHeap.freePoints rmwDemands values ∗ frame ⊢
      WP (ByteContentsHeap.script ctx (ByteContentsHeap.cycleActions memoryNode rmwDemands))
      {{ result, ⌜result = .ok finalState⌝ ∗ ByteContentsHeap.control finalState ∗
        ByteContentsHeap.freePoints rmwDemands (ByteContentsHeap.returnedValues rmwCandidate memoryNode values) ∗ frame }} := by
  apply ByteContentsHeap.cycle_local_wp ctx initialState finalState memoryNode rmwDemands values frame rmw_ready_from_empty
    rmw_footprint_actual_write_modes rmw_one_write_grant_per_byte initial_pool_has_actual_free_payloads
  rw [show Unified.memoryControlNode memoryNode = rmwNode from rfl,generic_grants_are_the_actual_four_claims]
  exact finish_checks_permissions_and_values

theorem local_cycle_has_closed_heap_initialization :
    adequate .NotStuck (ByteContentsHeap.script ctx (ByteContentsHeap.cycleActions memoryNode rmwDemands)) initialState
      (fun result _ => result = .ok finalState) := by
  apply ByteContentsHeap.cycle_local_adequate ctx initialState finalState memoryNode rmwDemands values rmw_ready_from_empty
    rmw_footprint_actual_write_modes rmw_one_write_grant_per_byte initial_pool_has_actual_free_payloads
  rw [show Unified.memoryControlNode memoryNode = rmwNode from rfl,generic_grants_are_the_actual_four_claims]
  exact finish_checks_permissions_and_values

def spare : Location := Ptx.ByteAcquisitionTests.frameLocation
def spareValue : Option Symbolic.Byte := some (.bits (byte 99))
def sparePayload : ByteContents.Payload := ⟨.available,spareValue⟩
def framedInitial := ByteContents.withSpare initialState spare spareValue
def framedAcquired := ByteContents.withSpare (acquiredState 4) spare spareValue
def framedFinal := ByteContents.finished rmwCandidate memoryNode rmwDemands framedAcquired

theorem spare_key_is_outside_actual_footprint : ByteAuthority.key spare ∉ ByteAuthority.Footprint.keys rmwDemands := by
  intro hm
  obtain ⟨demand,hm,he⟩ := List.mem_map.mp hm
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hm
  have ha := congrArg Location.address (ByteAuthority.key_injective he)
  change 64+index.val = 4096 at ha
  have hb := index.isLt
  omega

theorem framed_initial_has_real_extra_payload : get? framedInitial.cells (ByteAuthority.key spare) = some sparePayload := by
  simp [framedInitial,ByteContents.withSpare,sparePayload,get?_insert]

theorem framed_initial_keeps_every_accessed_payload : ByteContentsHeap.Free framedInitial rmwDemands values :=
  ByteContentsHeap.free_withSpare initial_pool_has_actual_free_payloads spare_key_is_outside_actual_footprint

theorem framed_grants_are_real_claim_states :
    ByteContentsHeap.granted framedInitial rmwNode rmwDemands values = framedAcquired := by
  rw [framedInitial,ByteContentsHeap.granted_withSpare _ _ _ _ _ _ spare_key_is_outside_actual_footprint,generic_grants_are_the_actual_four_claims]
  rfl

theorem adding_spare_preserves_all_source_and_value_checks :
    ByteContents.finish .one rmwCandidate (fun _ => []) memoryNode rmwDemands framedAcquired = .ok framedFinal :=
  ByteContents.finish_withSpare finish_checks_permissions_and_values spare_key_is_outside_actual_footprint

theorem framed_acquired_payloads_match_local_rule : ByteContentsHeap.Matches framedAcquired rmwNode rmwDemands values := by
  have hm := ByteContentsHeap.granted_matches framedInitial rmwNode rmwDemands values rmw_one_write_grant_per_byte
  rw [framed_grants_are_real_claim_states] at hm
  exact hm

theorem spare_value_is_unchanged_in_actual_final_state : get? framedFinal.cells (ByteAuthority.key spare) = some sparePayload :=
  ByteContents.finished_spare_unchanged spare_key_is_outside_actual_footprint

theorem actual_written_counter_still_one_with_extra_cell : ByteContents.valueAt framedFinal AtomicMemoryTests.base = some (.bits (byte 1)) := by
  have hm := ByteAuthority.Footprint.span_member AtomicMemoryTests.base 4 .write ⟨0,by decide⟩
  have hg := ByteContents.finishCells_member (candidate := rmwCandidate) (node := memoryNode) rmw_one_write_grant_per_byte hm
    (framed_acquired_payloads_match_local_rule _ hm)
  change get? framedFinal.cells (ByteAuthority.key AtomicMemoryTests.base) = some ⟨.available,some (.bits (byte 1))⟩ at hg
  unfold ByteContents.valueAt
  rw [hg]
  rfl

theorem native_cycle_frames_half_of_unrelated_byte [ByteContentsHeap.GS] :
    ByteContentsHeap.control framedInitial ∗ ByteContentsHeap.freePoints rmwDemands values ∗
      ByteContentsHeap.byte spare (.own (1 : Qp).half) sparePayload ⊢
      WP (ByteContentsHeap.script ctx (ByteContentsHeap.cycleActions memoryNode rmwDemands))
      {{ result, ⌜result = .ok framedFinal⌝ ∗ ByteContentsHeap.control framedFinal ∗
        ByteContentsHeap.freePoints rmwDemands (ByteContentsHeap.returnedValues rmwCandidate memoryNode values) ∗
        ByteContentsHeap.byte spare (.own (1 : Qp).half) sparePayload }} := by
  apply ByteContentsHeap.cycle_local_wp ctx framedInitial framedFinal memoryNode rmwDemands values _ rmw_ready_from_empty
    rmw_footprint_actual_write_modes rmw_one_write_grant_per_byte framed_initial_keeps_every_accessed_payload
  rw [show Unified.memoryControlNode memoryNode = rmwNode from rfl,framed_grants_are_real_claim_states]
  exact adding_spare_preserves_all_source_and_value_checks

theorem framed_precondition_comes_from_actual_heap [ByteContentsHeap.GS] :
    ByteContentsHeap.allPoints framedInitial ⊢ ByteContentsHeap.control framedInitial ∗ ByteContentsHeap.freePoints rmwDemands values ∗
      ByteContentsHeap.byte spare (.own 1) sparePayload :=
  ByteContentsHeap.allPoints_control_free_frame _ _ _ _ _ rmw_one_write_grant_per_byte framed_initial_keeps_every_accessed_payload
    spare_key_is_outside_actual_footprint framed_initial_has_real_extra_payload

theorem fractional_frame_cycle_closed_adequate :
    adequate .NotStuck (ByteContentsHeap.script ctx (ByteContentsHeap.cycleActions memoryNode rmwDemands)) framedInitial
      (fun result _ => result = .ok framedFinal) := by
  apply ByteContentsHeap.heap_adequacy
  intro _
  iintro Hall
  icases framed_precondition_comes_from_actual_heap $$ Hall with ⟨Hcontrol,Hfree,Hspare⟩
  icases ByteContentsHeap.byte_split spare 1 sparePayload $$ Hspare with ⟨Hleft,Hright⟩
  ihave Hwp := native_cycle_frames_half_of_unrelated_byte $$ [$Hcontrol $Hfree $Hleft]
  iapply wp_mono ?_ $$ Hwp
  intro result
  iintro ⟨%hv,Hcontrol,Hfree,Hspare⟩
  ipureintro; exact hv

theorem wrong_data_has_no_successful_local_completion :
    ∀ next, ByteContentsHeap.transition ctx (.finish memoryNode rmwDemands) wrongReadState ≠ .ok next := by
  intro next hs
  change ByteContents.finish .one rmwCandidate (fun _ => []) memoryNode rmwDemands wrongReadState = .ok next at hs
  rw [wrong_data_is_rejected_despite_full_authority] at hs
  cases hs

theorem incomplete_atomic_footprint_still_has_no_successful_completion :
    ∀ next, ByteContentsHeap.transition ctx (.finish memoryNode (ByteAuthority.Footprint.span AtomicMemoryTests.base 3 .write)) (acquiredState 4) ≠ .ok next := by
  intro next hs
  rw [show ByteContentsHeap.transition ctx (.finish memoryNode (ByteAuthority.Footprint.span AtomicMemoryTests.base 3 .write)) (acquiredState 4) =
    .error (.authority .unavailable) from incomplete_atomic_footprint_is_rejected] at hs
  cases hs

end
end Ptx.ByteContentsFootprintTests
