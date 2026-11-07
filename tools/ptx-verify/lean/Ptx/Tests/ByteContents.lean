import Ptx.Iris.ByteContents
import Ptx.Tests.ByteExecution

/-! Actual RMW read/write values, checked against an admitted real source
execution and coupled to byte authority. This is an event-local heap witness;
no SC realization of arbitrary PTX weak-memory executions is asserted.
-/
namespace Ptx.ByteContentsTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
open Ptx.ByteRetirementTests Ptx.ByteAcquisitionTests Ptx.ByteExecutionTests
noncomputable section

def memoryNode : Unified.Node := .base (.tma (.source AtomicMemoryTests.event))
def initial : Location → Symbolic.Byte := fun _ => .bits (byte 0)
def initialState : ByteContents.State :=
  ⟨⟨Ptx.Async.initial 0 [],fun _ => False⟩,ByteContents.initialCells rmwLocations initial⟩
def request (index : Nat) : ByteAuthority.Claim := ⟨rmwNode,AtomicMemoryTests.base.add index,.write⟩
def acquiredState : Nat → ByteContents.State
  | 0 => initialState
  | n+1 => ByteContents.claimed (acquiredState n) (request n) ⟨.available,some (.bits (byte 0))⟩
def ctx : ByteContentsHeap.Context := ⟨.one,rmwCandidate,fun _ => []⟩
def actions : List ByteContentsHeap.Action :=
  [.claim (request 0),.claim (request 1),.claim (request 2),.claim (request 3),.finish memoryNode rmwDemands]
def finalState := ByteContents.finished rmwCandidate memoryNode rmwDemands (acquiredState 4)

theorem read_event_matches_admitted_scalar_execution (loc : Location) :
    ByteContents.readByte rmwCandidate memoryNode loc = AtomicMemoryTests.graph.readByte AtomicMemoryTests.event loc := by rfl
theorem write_event_matches_admitted_scalar_execution (loc : Location) :
    ByteContents.writeByte rmwCandidate memoryNode loc = AtomicMemoryTests.graph.writeByte AtomicMemoryTests.event loc := by rfl

theorem emitted_read_value_from_actual_memory_conditions {loc value}
    (hr : ByteContents.readByte rmwCandidate memoryNode loc = some value) : value = initial loc := by
  rw [read_event_matches_admitted_scalar_execution] at hr
  have he := Ptx.Event.race_free_eligible AtomicMemoryTests.no_races AtomicMemoryTests.event loc
  have ha := AtomicMemoryTests.consistent.agreement AtomicMemoryTests.event loc value he hr
  change some (initial loc) = some value at ha
  exact (Option.some.inj ha).symm

theorem emitted_read_location_is_in_initial_pool {loc value}
    (hr : ByteContents.readByte rmwCandidate memoryNode loc = some value) : loc ∈ rmwLocations := by
  exact actual_rmw_locations_bound_all_node_uses loc .read
    ⟨.kernel,.kernel (ordinary_read_use hr)⟩

theorem actual_initial_value_at_every_emitted_read {loc value}
    (hr : ByteContents.readByte rmwCandidate memoryNode loc = some value) : ByteContents.valueAt initialState loc = some value := by
  have hg := ByteContents.initialCells_member (initial := initial) (emitted_read_location_is_in_initial_pool hr)
  change (get? (ByteContents.initialCells rmwLocations initial) (ByteAuthority.key loc)).bind ByteContents.Payload.value = some value
  rw [hg]
  exact congrArg some (emitted_read_value_from_actual_memory_conditions hr).symm

theorem each_claim_has_available_actual_value (index : Fin 4) :
    get? (acquiredState index.val).cells (ByteAuthority.key ((request index.val).location)) = some ⟨.available,some (.bits (byte 0))⟩ := by
  fin_cases index <;> simp [acquiredState,ByteContents.claimed,ByteContents.initialCells,initialState,rmwLocations,rmwDemands,
    ByteAuthority.Footprint.span,request,AtomicMemoryTests.base,Location.add,initial,get?_insert,ByteAuthority.key,Nat.pair]

theorem acquired_coupled (n : Nat) : (acquiredState n).coupled = initialState.coupled := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem actual_claim_succeeds (index : Fin 4) :
    ByteContents.claim .one rmwCandidate (fun _ => []) (request index.val) (acquiredState index.val) = .ok (acquiredState (index.val+1)) := by
  have hr : ByteAuthority.Ready .one rmwCandidate (fun _ => []) (acquiredState index.val).coupled.done (request index.val).node := by
    rw [acquired_coupled]
    exact rmw_ready_from_empty
  apply ByteContents.claim_succeeds hr
  · exact rmw_footprint_actual_write_modes _ (ByteAuthority.Footprint.span_member _ _ _ index)
  · exact each_claim_has_available_actual_value index

theorem value_effect_is_linked_to_actual_permission_use : ByteContents.Linked rmwCandidate memoryNode := by
  refine ⟨⟨?_,?_⟩,ByteContents.ordinary_complete_at actual_rmw_source_lookup⟩
  · intro loc value hr
    exact ⟨.kernel,.kernel (ordinary_read_use hr)⟩
  · intro loc value hw
    exact ⟨.kernel,.kernel (ordinary_write_use hw)⟩

theorem acquired_values_are_still_initial (index : Fin 4) :
    get? (acquiredState 4).cells (ByteAuthority.key (AtomicMemoryTests.base.add index.val)) =
      some ⟨.held rmwNode .write,some (.bits (byte 0))⟩ := by
  fin_cases index <;> simp [acquiredState,ByteContents.claimed,ByteContents.initialCells,initialState,rmwLocations,rmwDemands,
    ByteAuthority.Footprint.span,request,AtomicMemoryTests.base,Location.add,initial,get?_insert,ByteAuthority.key,Nat.pair]

theorem value_check_uses_actual_admitted_reads : ByteContents.Reads rmwCandidate memoryNode (acquiredState 4) := by
  intro loc value hr
  have hl := emitted_read_location_is_in_initial_pool hr
  obtain ⟨demand,hm,he⟩ := List.mem_map.mp hl
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hm
  subst loc
  unfold ByteContents.valueAt
  rw [acquired_values_are_still_initial index]
  exact congrArg some (emitted_read_value_from_actual_memory_conditions hr).symm

theorem acquired_permissions_complete :
    ByteAuthority.Footprint.Held (ByteContents.erase (acquiredState 4)) rmwNode rmwDemands := by
  intro demand hm
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hm
  change get? (Iris.Std.PartialMap.map ByteContents.Payload.owner (acquiredState 4).cells) _ = _
  rw [get?_map,acquired_values_are_still_initial index]
  rfl

theorem acquired_permission_frame : ByteAuthority.Footprint.Frame (ByteContents.erase (acquiredState 4)) rmwNode rmwDemands := by
  intro k mode hg
  change get? (Iris.Std.PartialMap.map ByteContents.Payload.owner (acquiredState 4).cells) k = _ at hg
  rw [get?_map] at hg
  simp only [acquiredState,ByteContents.claimed,get?_insert] at hg
  split at hg
  · rename_i he
    exact List.mem_map.mpr ⟨⟨AtomicMemoryTests.base.add 3,.write⟩,ByteAuthority.Footprint.span_member _ _ _ ⟨3,by decide⟩,he⟩
  · split at hg
    · rename_i he
      exact List.mem_map.mpr ⟨⟨AtomicMemoryTests.base.add 2,.write⟩,ByteAuthority.Footprint.span_member _ _ _ ⟨2,by decide⟩,he⟩
    · split at hg
      · rename_i he
        exact List.mem_map.mpr ⟨⟨AtomicMemoryTests.base.add 1,.write⟩,ByteAuthority.Footprint.span_member _ _ _ ⟨1,by decide⟩,he⟩
      · split at hg
        · rename_i he
          exact List.mem_map.mpr ⟨⟨AtomicMemoryTests.base.add 0,.write⟩,ByteAuthority.Footprint.span_member _ _ _ ⟨0,by decide⟩,he⟩
        · have ho : ∀ k p, get? initialState.cells k = some p → p.owner = .available := by
            intro key payload hlookup
            exact ByteContents.initialCells_owner_available hlookup
          cases hx : get? initialState.cells k with
          | none => simp [hx] at hg
          | some payload =>
            have hv := ho k payload hx
            simp only [hx,Option.map_some,Option.some.injEq] at hg
            rw [hg] at hv
            cases hv

theorem finish_checks_permissions_and_values :
    ByteContents.finish .one rmwCandidate (fun _ => []) memoryNode rmwDemands (acquiredState 4) = .ok finalState := by
  apply ByteContents.finish_succeeds
  · exact ByteAuthority.Footprint.finish_succeeds rmw_ready_from_empty rmw_footprint_actual_write_modes rmw_footprint_complete
      rmw_one_write_grant_per_byte acquired_permissions_complete acquired_permission_frame
  · exact value_effect_is_linked_to_actual_permission_use
  · exact value_check_uses_actual_admitted_reads

theorem actual_value_script_run : IrisExecution.run (ByteContentsHeap.transition ctx) actions initialState = .ok finalState := by
  change (ByteContents.claim .one rmwCandidate (fun _ => []) (request 0) (acquiredState 0)).bind _ = _
  rw [actual_claim_succeeds ⟨0,by decide⟩]
  change (ByteContents.claim .one rmwCandidate (fun _ => []) (request 1) (acquiredState 1)).bind _ = _
  rw [actual_claim_succeeds ⟨1,by decide⟩]
  change (ByteContents.claim .one rmwCandidate (fun _ => []) (request 2) (acquiredState 2)).bind _ = _
  rw [actual_claim_succeeds ⟨2,by decide⟩]
  change (ByteContents.claim .one rmwCandidate (fun _ => []) (request 3) (acquiredState 3)).bind _ = _
  rw [actual_claim_succeeds ⟨3,by decide⟩]
  change (ByteContents.finish .one rmwCandidate (fun _ => []) memoryNode rmwDemands (acquiredState 4)).bind _ = _
  rw [finish_checks_permissions_and_values]
  rfl

theorem native_value_script_closed_adequate :
    adequate .NotStuck (ByteContentsHeap.script ctx actions) initialState (fun value _ => value = .ok finalState) :=
  ByteContentsHeap.script_adequate ctx actions initialState finalState actual_value_script_run

theorem written_counter_matches_actual_event_and_observer :
    ByteContents.valueAt finalState AtomicMemoryTests.base =
      (Ptx.Event.singleWriterObservation AtomicMemoryTests.graph AtomicMemoryTests.initial AtomicMemoryTests.event AtomicMemoryTests.domain).output AtomicMemoryTests.base := by
  have hm := ByteAuthority.Footprint.span_member AtomicMemoryTests.base 4 .write ⟨0,by decide⟩
  have hg := ByteContents.finishCells_member (candidate := rmwCandidate) (node := memoryNode) rmw_one_write_grant_per_byte hm
    (acquired_values_are_still_initial ⟨0,by decide⟩)
  change (get? (ByteContents.finishCells rmwCandidate memoryNode rmwDemands (acquiredState 4).cells) (ByteAuthority.key AtomicMemoryTests.base)).bind _ = _
  change get? (ByteContents.finishCells rmwCandidate memoryNode rmwDemands (acquiredState 4).cells)
    (ByteAuthority.key AtomicMemoryTests.base) = some ⟨.available,some (.bits (byte 1))⟩ at hg
  rw [hg]
  rfl

theorem authority_finish_passes_before_value_checks :
    ByteAuthority.Footprint.finish .one rmwCandidate (fun _ => []) rmwNode rmwDemands (ByteContents.erase (acquiredState 4)) =
      .ok (ByteAuthority.retired (ByteContents.erase (acquiredState 4)) rmwNode) :=
  ByteAuthority.Footprint.finish_succeeds rmw_ready_from_empty rmw_footprint_actual_write_modes rmw_footprint_complete
    rmw_one_write_grant_per_byte acquired_permissions_complete acquired_permission_frame

def wrongReadState := ByteContents.withValue (acquiredState 4) AtomicMemoryTests.base (some (.bits (byte 1)))
def uninitializedReadState := ByteContents.withValue (acquiredState 4) AtomicMemoryTests.base none

theorem wrong_contents_keep_all_permissions : ByteContents.erase wrongReadState = ByteContents.erase (acquiredState 4) :=
  ByteContents.erase_withValue _ _ _
theorem uninitialized_contents_keep_all_permissions : ByteContents.erase uninitializedReadState = ByteContents.erase (acquiredState 4) :=
  ByteContents.erase_withValue _ _ _

theorem wrong_contents_cannot_realize_emitted_read : ¬ByteContents.Reads rmwCandidate memoryNode wrongReadState := by
  intro hr
  have hread := hr AtomicMemoryTests.base (.bits (byte 0)) (by rfl)
  have hv : ByteContents.valueAt wrongReadState AtomicMemoryTests.base = some (.bits (byte 1)) :=
    ByteContents.withValue_lookup (acquired_values_are_still_initial ⟨0,by decide⟩)
  have hb := Symbolic.Byte.bits.inj (Option.some.inj (hv.symm.trans hread))
  have hn := congrArg Fin.val hb
  norm_num [byte] at hn

theorem uninitialized_contents_cannot_realize_emitted_read : ¬ByteContents.Reads rmwCandidate memoryNode uninitializedReadState := by
  intro hr
  have hread := hr AtomicMemoryTests.base (.bits (byte 0)) (by rfl)
  have hv : ByteContents.valueAt uninitializedReadState AtomicMemoryTests.base = none :=
    ByteContents.withValue_lookup (acquired_values_are_still_initial ⟨0,by decide⟩)
  rw [hv] at hread
  cases hread

theorem wrong_data_is_rejected_despite_full_authority :
    ByteContents.finish .one rmwCandidate (fun _ => []) memoryNode rmwDemands wrongReadState = .error .readMismatch := by
  simp only [ByteContents.finish,wrong_contents_keep_all_permissions,
    value_effect_is_linked_to_actual_permission_use,wrong_contents_cannot_realize_emitted_read,ite_true,ite_false]
  rw [show Unified.memoryControlNode memoryNode = rmwNode from rfl,authority_finish_passes_before_value_checks]

theorem uninitialized_data_is_rejected_despite_full_authority :
    ByteContents.finish .one rmwCandidate (fun _ => []) memoryNode rmwDemands uninitializedReadState = .error .readMismatch := by
  simp only [ByteContents.finish,uninitialized_contents_keep_all_permissions,
    value_effect_is_linked_to_actual_permission_use,uninitialized_contents_cannot_realize_emitted_read,ite_true,ite_false]
  rw [show Unified.memoryControlNode memoryNode = rmwNode from rfl,authority_finish_passes_before_value_checks]

theorem value_finish_projects_to_existing_permissions :
    ByteAuthority.Step .one rmwCandidate (fun _ => []) (fun _ _ => False) (fun _ => none)
      (ByteContents.erase (acquiredState 4)) (ByteContents.erase finalState) :=
  ByteContents.finish_projects finish_checks_permissions_and_values

theorem complete_value_script_projects_to_existing_permissions :
    ByteAuthority.Steps .one rmwCandidate (fun _ => []) (fun _ _ => False) (fun _ => none)
      (ByteContents.erase initialState) (ByteContents.erase finalState) :=
  ByteContentsHeap.run_projects ctx actions actual_value_script_run

theorem final_value_cell_has_returned_authority (index : Fin 4) :
    get? finalState.cells (ByteAuthority.key (AtomicMemoryTests.base.add index.val)) =
      some ⟨.available,(ByteContents.writeByte rmwCandidate memoryNode (AtomicMemoryTests.base.add index.val)).or (some (.bits (byte 0)))⟩ :=
  ByteContents.finishCells_member rmw_one_write_grant_per_byte (ByteAuthority.Footprint.span_member _ _ _ index)
    (acquired_values_are_still_initial index)

theorem source_advances_after_atomic_value_update : finalState.coupled.done rmwNode := Or.inr rfl

theorem native_value_script_frames_resources [ByteContentsHeap.GS] (frame : IProp ByteContentsHeap.GF) :
    ByteContentsHeap.allPoints initialState ∗ frame ⊢ WP (ByteContentsHeap.script ctx actions)
      {{ value, ⌜value = .ok finalState⌝ ∗ ByteContentsHeap.allPoints finalState ∗ frame }} :=
  ByteContentsHeap.script_wp ctx actions initialState finalState frame actual_value_script_run

theorem native_counter_fragment_contains_actual_written_value [ByteContentsHeap.GS] (frame : IProp ByteContentsHeap.GF) :
    ByteContentsHeap.allPoints initialState ∗ frame ⊢ WP (ByteContentsHeap.script ctx actions)
      {{ value, ⌜value = .ok finalState⌝ ∗ ByteContentsHeap.byte AtomicMemoryTests.base (.own 1) ⟨.available,some (.bits (byte 1))⟩ ∗ frame }} := by
  iintro H
  ihave Hwp := native_value_script_frames_resources frame $$ H
  iapply wp_mono ?_ $$ Hwp
  intro value
  iintro ⟨%hv,Hall,Hframe⟩
  have hg : get? finalState.cells (ByteAuthority.key AtomicMemoryTests.base) = some ⟨.available,some (.bits (byte 1))⟩ :=
    final_value_cell_has_returned_authority ⟨0,by decide⟩
  ihave Hbyte := ByteContentsHeap.allPoints_byte finalState AtomicMemoryTests.base _ hg $$ Hall
  isplit
  · ipureintro; exact hv
  · iframe Hbyte Hframe

theorem complete_value_script_has_five_semantic_actions : actions.length = 5 := rfl

theorem generic_ordinary_link_covers_real_rmw : ByteContents.Linked rmwCandidate memoryNode :=
  ByteContents.ordinary_linked actual_rmw_source_lookup

theorem three_byte_footprint_cannot_cover_rmw :
    ¬ByteAuthority.Footprint.Covers rmwCandidate rmwNode (ByteAuthority.Footprint.span AtomicMemoryTests.base 3 .write) := by
  intro hc
  have hu := rmw_footprint_actual_write_modes _ (ByteAuthority.Footprint.span_member AtomicMemoryTests.base 4 .write ⟨3,by decide⟩)
  obtain ⟨demand,hm,he,_⟩ := hc _ _ hu
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hm
  have ha := congrArg Location.address he
  change 64+index.val = 64+3 at ha
  have hb := index.isLt
  omega

theorem incomplete_atomic_footprint_is_rejected :
    ByteContents.finish .one rmwCandidate (fun _ => []) memoryNode (ByteAuthority.Footprint.span AtomicMemoryTests.base 3 .write) (acquiredState 4) =
      .error (.authority .unavailable) := by
  have hr : ByteAuthority.Ready .one rmwCandidate (fun _ => []) (ByteContents.erase (acquiredState 4)).coupled.done (Unified.memoryControlNode memoryNode) :=
    rmw_ready_from_empty
  have hbad : ByteAuthority.Footprint.finish .one rmwCandidate (fun _ => []) (Unified.memoryControlNode memoryNode)
      (ByteAuthority.Footprint.span AtomicMemoryTests.base 3 .write) (ByteContents.erase (acquiredState 4)) = .error .unavailable := by
    unfold ByteAuthority.Footprint.finish
    rw [if_pos hr]
    exact if_neg (fun h => three_byte_footprint_cannot_cover_rmw h.2.1)
  unfold ByteContents.finish
  rw [hbad]

theorem finished_source_cannot_repeat_value_update :
    ByteContents.finish .one rmwCandidate (fun _ => []) memoryNode rmwDemands finalState = .error (.authority .unready) := by
  have hn : ¬ByteAuthority.Ready .one rmwCandidate (fun _ => []) (ByteContents.erase finalState).coupled.done (Unified.memoryControlNode memoryNode) :=
    fun hr => hr.2.1 source_advances_after_atomic_value_update
  simp only [ByteContents.finish,ByteAuthority.Footprint.finish,hn,ite_false]

theorem unrelated_actual_byte_content_is_preserved :
    get? (ByteContents.finishCells rmwCandidate memoryNode rmwDemands
      (insert (acquiredState 4).cells (ByteAuthority.key Ptx.ByteAcquisitionTests.frameLocation) ⟨.available,some (.bits (byte 99))⟩))
      (ByteAuthority.key Ptx.ByteAcquisitionTests.frameLocation) = some ⟨.available,some (.bits (byte 99))⟩ := by
  have hn : ByteAuthority.key Ptx.ByteAcquisitionTests.frameLocation ∉ ByteAuthority.Footprint.keys rmwDemands := by
    intro hm
    obtain ⟨demand,hm,he⟩ := List.mem_map.mp hm
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hm
    have hl := ByteAuthority.key_injective he
    have ha := congrArg Location.address hl
    change 64+index.val = 4096 at ha
    have hb := index.isLt
    omega
  rw [ByteContents.finishCells_outside _ _ _ _ _ hn]
  simp [get?_insert]

end
end Ptx.ByteContentsTests
