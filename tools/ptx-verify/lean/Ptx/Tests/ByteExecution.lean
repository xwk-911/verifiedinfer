import Ptx.Iris.ByteInventory
import Ptx.Kernels.HopperDoubleBufferByteIris
import Ptx.Kernels.HopperDoubleBufferByteExecution
import Ptx.Tests.ByteAcquisition
import Ptx.Tests.HopperWholePlan

/-! Automatically selected footprints and whole finite source/protocol lifts.
These tests do not assert whole-kernel native Iris/value/runtime adequacy.
-/
namespace Ptx.ByteExecutionTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
open Ptx.ByteRetirementTests Ptx.ByteAcquisitionTests
noncomputable section

theorem write_selection_normalizes_duplicate_locations (candidate : Unified.Candidate) (node : Unified.ControlNode) (loc : Location)
    (hu : ByteAuthority.Uses candidate node loc .write) :
    ByteAuthority.Footprint.inventory candidate node [loc,loc] = [⟨loc,.write⟩] := by
  classical
  simp [ByteAuthority.Footprint.inventory,ByteAuthority.Footprint.select,hu]

theorem read_only_selection_stays_read (candidate : Unified.Candidate) (node : Unified.ControlNode) (loc : Location)
    (hr : ByteAuthority.Uses candidate node loc .read) (hw : ¬ByteAuthority.Uses candidate node loc .write) :
    ByteAuthority.Footprint.inventory candidate node [loc,loc] = [⟨loc,.read⟩] := by
  classical
  simp [ByteAuthority.Footprint.inventory,ByteAuthority.Footprint.select,hr,hw]

theorem unused_location_produces_no_claim (candidate : Unified.Candidate) (node : Unified.ControlNode) (loc : Location)
    (hr : ¬ByteAuthority.Uses candidate node loc .read) (hw : ¬ByteAuthority.Uses candidate node loc .write) :
    ByteAuthority.Footprint.inventory candidate node [loc] = [] := by
  classical
  simp [ByteAuthority.Footprint.inventory,ByteAuthority.Footprint.select,hr,hw]

theorem actual_rmw_read_write_demands_share_one_grant :
    ByteAuthority.Footprint.inventory rmwCandidate rmwNode [AtomicMemoryTests.base,AtomicMemoryTests.base] =
      [⟨AtomicMemoryTests.base,.write⟩] :=
  write_selection_normalizes_duplicate_locations _ _ _ actual_rmw_first_byte_write

theorem unrelated_global_byte_is_not_an_rmw_use (mode : Ptx.Async.Mode) :
    ¬ByteAuthority.Uses rmwCandidate rmwNode frameLocation mode := by
  intro hu
  have hb := (rmw_use_bounds hu).2.2
  change 4096 < 68 at hb
  omega

theorem unrelated_global_byte_generates_no_claim :
    ByteAuthority.Footprint.inventory rmwCandidate rmwNode [frameLocation] = [] :=
  unused_location_produces_no_claim _ _ _ (unrelated_global_byte_is_not_an_rmw_use .read)
    (unrelated_global_byte_is_not_an_rmw_use .write)

def rmwLocations : List Location := rmwDemands.map (fun demand => demand.location)

theorem actual_rmw_locations_bound_all_node_uses (loc : Location) (mode : Ptx.Async.Mode)
    (hu : ByteAuthority.Uses rmwCandidate rmwNode loc mode) : loc ∈ rmwLocations := by
  obtain ⟨demand,hm,he,_⟩ := rmw_footprint_complete loc mode hu
  exact List.mem_map.mpr ⟨demand,hm,he⟩

theorem actual_rmw_selected_footprint_complete :
    ByteAuthority.Footprint.Covers rmwCandidate rmwNode (ByteAuthority.Footprint.inventory rmwCandidate rmwNode rmwLocations) :=
  ByteAuthority.Footprint.inventory_covers actual_rmw_locations_bound_all_node_uses

theorem actual_rmw_selected_footprint_sound :
    ByteAuthority.Footprint.Sound rmwCandidate rmwNode (ByteAuthority.Footprint.inventory rmwCandidate rmwNode rmwLocations) :=
  ByteAuthority.Footprint.inventory_sound _ _ _

theorem actual_rmw_selected_keys_distinct :
    ByteAuthority.Footprint.Distinct (ByteAuthority.Footprint.inventory rmwCandidate rmwNode (rmwLocations ++ rmwLocations)) :=
  ByteAuthority.Footprint.inventory_distinct _ _ _

theorem empty_inventory_cannot_cover_actual_rmw :
    ¬ByteAuthority.Footprint.Covers rmwCandidate rmwNode (ByteAuthority.Footprint.inventory rmwCandidate rmwNode []) := by
  intro hc
  obtain ⟨demand,hm,_,_⟩ := hc _ _ actual_rmw_first_byte_read
  exact List.not_mem_nil (ByteAuthority.Footprint.inventory_location hm)

def rmwCoupled : Bridge.State := ⟨Ptx.Async.initial 0 [],fun _ => False⟩
def rmwContext : ByteAuthorityHeap.Context := {block := .one,candidate := rmwCandidate,histories := fun _ => [] }

theorem selected_rmw_script_runs_from_available_pool :
    IrisExecution.run (ByteAuthorityHeap.transition rmwContext)
      (ByteAuthorityHeap.cycleActions rmwNode (ByteAuthority.Footprint.inventory rmwCandidate rmwNode rmwLocations))
      (ByteAuthority.Footprint.initialized rmwCoupled rmwLocations) =
      .ok (ByteAuthority.Footprint.initialized {rmwCoupled with done := fun n => rmwCoupled.done n ∨ n = rmwNode} rmwLocations) :=
  ByteAuthorityHeap.inventory_cycle_run _ _ _ _ actual_rmw_locations_bound_all_node_uses rmw_ready_from_empty

theorem selected_rmw_script_closed_adequate :
    adequate .NotStuck
      (ByteAuthorityHeap.script rmwContext (ByteAuthorityHeap.cycleActions rmwNode (ByteAuthority.Footprint.inventory rmwCandidate rmwNode rmwLocations)))
      (ByteAuthority.Footprint.initialized rmwCoupled rmwLocations)
      (fun value _ => value = .ok (ByteAuthority.Footprint.initialized {rmwCoupled with done := fun n => rmwCoupled.done n ∨ n = rmwNode} rmwLocations)) :=
  ByteAuthorityHeap.inventory_cycle_adequate _ _ _ _ actual_rmw_locations_bound_all_node_uses rmw_ready_from_empty

theorem omitted_barrier_byte_still_prevents_complete_selection (slot : Stage) :
    ¬ByteAuthority.Footprint.Covers ByteAuthorityTests.candidate (barrierNode slot)
      (ByteAuthority.Footprint.inventory ByteAuthorityTests.candidate (barrierNode slot)
        ((ByteAuthority.Footprint.span (dataGate slot) 7 .write).map (fun demand => demand.location))) := by
  intro hc
  obtain ⟨demand,hm,he,_⟩ := hc _ _ (ByteAuthorityTests.actual_init_uses_storage slot 7)
  have hl := ByteAuthority.Footprint.inventory_location hm
  obtain ⟨original,ho,hlo⟩ := List.mem_map.mp hl
  obtain ⟨offset,rfl⟩ := List.mem_ofFn.mp ho
  have ha := congrArg Location.address (hlo.trans he)
  change (dataGate slot).address+offset.val = (dataGate slot).address+7 at ha
  have hb := offset.isLt
  omega

theorem source_data_family_all_uses_bounded (a b tiles schedules) (frame : Location → Symbolic.Byte)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ByteAuthority.Footprint.Bounded (retryDataCandidate a b tiles schedules)
      (Whole.byteLocations (retryDataFamily a b tiles schedules)) := by
  have htma := (retry_data_complete_components a b tiles schedules frame ht hb).1
  exact Whole.byte_inventory_bounded _ ht hb htma.source htma.complete htma.descriptors

theorem source_data_family_complete_authority_run (a b tiles schedules) (frame : Location → Symbolic.Byte)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ByteAuthority.Steps HopperStage.block (retryDataCandidate a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster (Whole.plan (retryDataFamily a b tiles schedules))
      (ByteAuthority.Footprint.initialized ⟨Whole.prepared HopperWholePlanTests.values tiles,fun _ => False⟩
        (Whole.byteLocations (retryDataFamily a b tiles schedules)))
      (ByteAuthority.Footprint.initialized ⟨Whole.returned HopperWholePlanTests.values tiles,Present (retryDataCandidate a b tiles schedules)⟩
        (Whole.byteLocations (retryDataFamily a b tiles schedules))) :=
  Whole.complete_byte_authority_run _ ht hb (retry_data_complete_components a b tiles schedules frame ht hb).1 _ rfl

theorem every_source_node_has_complete_automatically_selected_footprint (a b tiles schedules) (frame : Location → Symbolic.Byte)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (node : Unified.ControlNode) :
    ByteAuthority.Footprint.Covers (retryDataCandidate a b tiles schedules) node
      (ByteAuthority.Footprint.inventory (retryDataCandidate a b tiles schedules) node (Whole.byteLocations (retryDataFamily a b tiles schedules))) :=
  ByteAuthority.Footprint.inventory_covers (source_data_family_all_uses_bounded a b tiles schedules frame ht hb node)

theorem complete_run_preserves_original_source_and_protocol (a b tiles schedules) (frame : Location → Symbolic.Byte)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Bridge.Steps HopperStage.block Tma.localShared (retryDataCandidate a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster (Whole.plan (retryDataFamily a b tiles schedules))
      ⟨Whole.prepared HopperWholePlanTests.values tiles,fun _ => False⟩
      ⟨Whole.returned HopperWholePlanTests.values tiles,Present (retryDataCandidate a b tiles schedules)⟩ :=
  ByteAuthority.steps_projects (source_data_family_complete_authority_run a b tiles schedules frame ht hb)

theorem whole_final_pool_contains_no_held_authority {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (values : List Nat) (k : Nat) (node : Unified.ControlNode) (mode : Ptx.Async.Mode) :
    get? (ByteAuthority.Footprint.initialized ⟨Whole.returned values tiles,Present candidate⟩ (Whole.byteLocations family)).bytes k ≠
      some (.held node mode) := by
  intro hh
  have he := ByteAuthority.Footprint.initialized_available _ _ k _ hh
  cases he

theorem full_source_witness_exists_for_one_tile (frame : Location → Symbolic.Byte) :
    ByteAuthority.Steps HopperStage.block (retryDataCandidate 2 3 1 (fun _ _ => 0))
      (retryHistories (retryDataFamily 2 3 1 (fun _ _ => 0))) dataCluster (Whole.plan (retryDataFamily 2 3 1 (fun _ _ => 0)))
      (ByteAuthority.Footprint.initialized ⟨Whole.prepared HopperWholePlanTests.values 1,fun _ => False⟩
        (Whole.byteLocations (retryDataFamily 2 3 1 (fun _ _ => 0))))
      (ByteAuthority.Footprint.initialized ⟨Whole.returned HopperWholePlanTests.values 1,Present (retryDataCandidate 2 3 1 (fun _ _ => 0))⟩
        (Whole.byteLocations (retryDataFamily 2 3 1 (fun _ _ => 0)))) :=
  source_data_family_complete_authority_run _ _ _ _ frame (by decide) (by decide)

theorem already_completed_node_cannot_appear_in_source_script (ctx : ByteAuthorityHeap.Context) {before after nodes}
    (ho : ByteAuthority.Footprint.Ordered ctx.block ctx.candidate ctx.histories before nodes after)
    (node : Unified.ControlNode) (hd : before node) : node ∉ nodes :=
  fun hm => ByteAuthority.Footprint.ordered_fresh ho node hm hd

theorem repeated_source_node_is_rejected (ctx : ByteAuthorityHeap.Context) (before after : Cut) (node : Unified.ControlNode) :
    ¬ByteAuthority.Footprint.Ordered ctx.block ctx.candidate ctx.histories before [node,node] after := by
  intro ho
  have hn := ByteAuthority.Footprint.ordered_nodup ho
  simp at hn

theorem source_script_has_exact_completion_cut (ctx : ByteAuthorityHeap.Context) {before after nodes}
    (ho : ByteAuthority.Footprint.Ordered ctx.block ctx.candidate ctx.histories before nodes after) :
    ∀ node, after node ↔ before node ∨ node ∈ nodes := ByteAuthority.Footprint.ordered_done ho

theorem full_source_native_witness_for_data_family (a b tiles schedules) (frame : Location → Symbolic.Byte)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∃ nodes, ByteAuthority.Footprint.Ordered HopperStage.block (retryDataCandidate a b tiles schedules)
        (retryHistories (retryDataFamily a b tiles schedules)) (fun _ => False) nodes (Present (retryDataCandidate a b tiles schedules)) ∧
      IrisExecution.run (ByteAuthorityHeap.transition (Whole.byteContext (retryDataFamily a b tiles schedules)))
        (ByteAuthorityHeap.sourceActions (Whole.byteContext (retryDataFamily a b tiles schedules)) (Whole.byteLocations (retryDataFamily a b tiles schedules)) nodes)
        (ByteAuthority.Footprint.initialized ⟨Whole.prepared HopperWholePlanTests.values tiles,fun _ => False⟩ (Whole.byteLocations (retryDataFamily a b tiles schedules))) =
        .ok (ByteAuthority.Footprint.initialized ⟨Whole.prepared HopperWholePlanTests.values tiles,Present (retryDataCandidate a b tiles schedules)⟩ (Whole.byteLocations (retryDataFamily a b tiles schedules))) ∧
      adequate .NotStuck
        (ByteAuthorityHeap.script (Whole.byteContext (retryDataFamily a b tiles schedules))
          (ByteAuthorityHeap.sourceActions (Whole.byteContext (retryDataFamily a b tiles schedules)) (Whole.byteLocations (retryDataFamily a b tiles schedules)) nodes))
        (ByteAuthority.Footprint.initialized ⟨Whole.prepared HopperWholePlanTests.values tiles,fun _ => False⟩ (Whole.byteLocations (retryDataFamily a b tiles schedules)))
        (fun value _ => value = .ok (ByteAuthority.Footprint.initialized ⟨Whole.prepared HopperWholePlanTests.values tiles,Present (retryDataCandidate a b tiles schedules)⟩ (Whole.byteLocations (retryDataFamily a b tiles schedules)))) :=
  Whole.complete_source_native_witness _ ht hb (retry_data_complete_components a b tiles schedules frame ht hb).1 _

theorem selected_node_retains_every_pool_fragment [ByteAuthorityHeap.GS]
    (ctx : ByteAuthorityHeap.Context) (coupled : Bridge.State) (locations : List Location) (node : Unified.ControlNode)
    (hb : ByteAuthority.Footprint.Bounded ctx.candidate locations)
    (hr : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories coupled.done node) (frame : IProp ByteAuthorityHeap.GF) :
    ByteAuthorityHeap.allPoints (ByteAuthority.Footprint.initialized coupled locations) ∗ frame ⊢
      WP (ByteAuthorityHeap.script ctx (ByteAuthorityHeap.sourceActions ctx locations [node]))
      {{ value, ⌜value = .ok (ByteAuthority.Footprint.initialized {coupled with done := fun n => coupled.done n ∨ n = node} locations)⌝ ∗
        ByteAuthorityHeap.allPoints (ByteAuthority.Footprint.initialized {coupled with done := fun n => coupled.done n ∨ n = node} locations) ∗ frame }} := by
  cases coupled with
  | mk protocol done => exact ByteAuthorityHeap.source_wp ctx locations protocol hb (.cons hr (.nil _)) frame

theorem sequential_nodes_can_reuse_the_same_pool [ByteAuthorityHeap.GS]
    (ctx : ByteAuthorityHeap.Context) (protocol : Ptx.Async.State) (locations : List Location) (before : Cut)
    (first second : Unified.ControlNode) (hb : ByteAuthority.Footprint.Bounded ctx.candidate locations)
    (hfirst : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories before first)
    (hsecond : ByteAuthority.Ready ctx.block ctx.candidate ctx.histories (fun n => before n ∨ n = first) second)
    (frame : IProp ByteAuthorityHeap.GF) :
    ByteAuthorityHeap.allPoints (ByteAuthority.Footprint.initialized ⟨protocol,before⟩ locations) ∗ frame ⊢
      WP (ByteAuthorityHeap.script ctx (ByteAuthorityHeap.sourceActions ctx locations [first,second]))
      {{ value, ⌜value = .ok (ByteAuthority.Footprint.initialized ⟨protocol,fun n => (before n ∨ n = first) ∨ n = second⟩ locations)⌝ ∗
        ByteAuthorityHeap.allPoints (ByteAuthority.Footprint.initialized ⟨protocol,fun n => (before n ∨ n = first) ∨ n = second⟩ locations) ∗ frame }} :=
  ByteAuthorityHeap.source_wp ctx locations protocol hb (.cons hfirst (.cons hsecond (.nil _))) frame

end
end Ptx.ByteExecutionTests
