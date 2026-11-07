import Ptx.Kernels.HopperDoubleBufferByteControl
import Ptx.Tests.ByteContentsFootprint
import Ptx.Tests.HopperRetryDataMemory
import Ptx.Tests.ByteAuthority

/-! Real native arrivals with reachable source cuts, explicit byte heaps and
native controller-only framing. These local witnesses do not simulate the
memory effects preceding the ranked cuts.
-/
namespace Ptx.ByteContentsControlTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

abbrev family := HopperRetryDataTests.family
abbrev candidate := HopperRetryDataTests.candidate
abbrev source := HopperRetryDataMemoryTests.source
abbrev components := HopperRetryDataMemoryTests.positive_joint_components
def ctx (a b) := byteContentsContext (family a b)
def node (a : TileA) (b : TileB) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) : Unified.ControlNode := .arrival ((family a b).nativeId tile lane index)
def spare : Location := ByteContentsFootprintTests.spare
def initial : Location → Symbolic.Byte := fun _ => .bits (byte 99)
def payload : ByteContents.Payload := ⟨.available,some (.bits (byte 99))⟩
def state (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) := byteArrivalState (family a b) tile lane index [spare] initial
def next (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) := ByteContents.controlFinished (state a b tile lane index) (node a b tile lane index)
def heldState (a : TileA) (b : TileB) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) : ByteContents.State :=
  let s := state a b tile lane index
  {s with cells := insert s.cells (ByteAuthority.key spare) ⟨.held (node a b tile lane index) .read,some (.bits (byte 99))⟩}

theorem every_starting_cut_has_actual_source_prefix (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) :
    Reached HopperStage.block (candidate a b) (retryHistories (family a b)) (state a b tile lane index).coupled.done :=
  retry_byte_arrival_prefix (family a b) (by decide) (by decide) (source a b) (components a b).1.histories_valid tile lane index

theorem all_actual_arrivals_pass_original_checks (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) :
    ByteContents.finishControl HopperStage.block (candidate a b) (retryHistories (family a b)) (node a b tile lane index)
      (state a b tile lane index) = .ok (next a b tile lane index) :=
  retry_byte_arrival_finishes (family a b) (by decide) (by decide) (source a b) (components a b).1.histories_valid tile tile.isLt lane index [spare] initial

theorem all_actual_arrival_scripts_succeed (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) :
    IrisExecution.run (ByteContentsHeap.transition (ctx a b)) [.control (node a b tile lane index)] (state a b tile lane index) = .ok (next a b tile lane index) :=
  retry_byte_arrival_script_run (family a b) (by decide) (by decide) (source a b) (components a b).1.histories_valid tile tile.isLt lane index [spare] initial

theorem allocated_spare_has_real_payload (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) :
    get? (state a b tile lane index).cells (ByteAuthority.key spare) = some payload :=
  ByteContents.initialCells_member (by simp)

theorem every_byte_value_is_preserved (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) (loc : Location) :
    ByteContents.valueAt (next a b tile lane index) loc = ByteContents.valueAt (state a b tile lane index) loc :=
  ByteContents.finishControl_preserves_value (all_actual_arrivals_pass_original_checks a b tile lane index) loc

theorem allocated_spare_stays_ninety_nine (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) :
    ByteContents.valueAt (next a b tile lane index) spare = some (.bits (byte 99)) := by
  rw [every_byte_value_is_preserved]
  unfold ByteContents.valueAt
  rw [allocated_spare_has_real_payload]
  rfl

theorem source_cut_remains_valid (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) :
    Valid HopperStage.block (candidate a b) (retryHistories (family a b)) (next a b tile lane index).coupled.done :=
  ByteContentsHeap.run_valid (ctx a b) _ (reached_valid (every_starting_cut_has_actual_source_prefix a b tile lane index))
    (all_actual_arrival_scripts_succeed a b tile lane index)

theorem control_step_projects_to_existing_authority (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) (plan : Bridge.Plan) :
    ByteAuthority.Step HopperStage.block (candidate a b) (retryHistories (family a b)) dataCluster plan
      (ByteContents.erase (state a b tile lane index)) (ByteContents.erase (next a b tile lane index)) :=
  ByteContents.finishControl_projects (all_actual_arrivals_pass_original_checks a b tile lane index)

theorem native_arrival_keeps_fractional_spare [ByteContentsHeap.GS] (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) :
    ByteContentsHeap.control (state a b tile lane index) ∗ ByteContentsHeap.byte spare (.own (1 : Qp).half) payload ⊢
      WP (ByteContentsHeap.script (ctx a b) [.control (node a b tile lane index)])
      {{ result, ⌜result = .ok (next a b tile lane index)⌝ ∗ ByteContentsHeap.control (next a b tile lane index) ∗
        ByteContentsHeap.byte spare (.own (1 : Qp).half) payload }} :=
  ByteContentsHeap.control_local_wp (ctx a b) (state a b tile lane index) (node a b tile lane index) _
    (all_actual_arrivals_pass_original_checks a b tile lane index)

theorem fractional_arrival_closed_adequate (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) :
    adequate .NotStuck (ByteContentsHeap.script (ctx a b) [.control (node a b tile lane index)]) (state a b tile lane index)
      (fun result _ => result = .ok (next a b tile lane index)) := by
  apply ByteContentsHeap.heap_adequacy
  intro _
  iintro Hall
  have hf : ByteContentsHeap.Free (state a b tile lane index) [] (fun _ => none) := by intro _ hm; cases hm
  icases ByteContentsHeap.allPoints_control_free_frame (state a b tile lane index) [] (fun _ => none) spare payload
    (show ByteAuthority.Footprint.Distinct [] from List.nodup_nil) hf (by simp [ByteAuthority.Footprint.keys])
    (allocated_spare_has_real_payload a b tile lane index) $$ Hall with ⟨Hcontrol,Hfree,Hspare⟩
  icases ByteContentsHeap.byte_split spare 1 payload $$ Hspare with ⟨Hleft,Hright⟩
  ihave Hwp := native_arrival_keeps_fractional_spare a b tile lane index $$ [$Hcontrol $Hleft]
  iapply wp_mono ?_ $$ Hwp
  intro result
  iintro ⟨%hv,Hcontrol,Hspare⟩
  ipureintro; exact hv

theorem repeated_arrival_is_rejected (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) :
    ByteContents.finishControl HopperStage.block (candidate a b) (retryHistories (family a b)) (node a b tile lane index)
      (next a b tile lane index) = .error (.authority .unready) := by
  apply ByteContents.finishControl_unready
  intro hr
  exact hr.2.1 (Or.inr rfl)

theorem actual_rmw_read_cannot_be_control_only :
    ∀ next, ByteContents.finishControl .one ByteRetirementTests.rmwCandidate (fun _ => []) ByteRetirementTests.rmwNode
      (ByteContentsTests.acquiredState 4) ≠ .ok next :=
  ByteContents.finishControl_rejects_actual_read (memory := ByteContentsTests.memoryNode) rfl (loc := AtomicMemoryTests.base) (by rfl)

theorem actual_rmw_write_cannot_be_control_only :
    ∀ next, ByteContents.finishControl .one ByteRetirementTests.rmwCandidate (fun _ => []) ByteRetirementTests.rmwNode
      (ByteContentsTests.acquiredState 4) ≠ .ok next :=
  ByteContents.finishControl_rejects_actual_write (memory := ByteContentsTests.memoryNode) rfl (loc := AtomicMemoryTests.base) (by rfl)

theorem actual_resource_storage_cannot_be_control_only (slot : Stage) (state : ByteContents.State) :
    ∀ next, ByteContents.finishControl HopperStage.block ByteAuthorityTests.candidate zeroHistories (ByteAuthorityTests.node slot) state ≠ .ok next :=
  ByteContents.finishControl_rejects_source_use (ByteAuthorityTests.actual_init_uses_storage slot 0)

theorem ordinary_rmw_cannot_invent_native_arrival :
    ByteContents.finishControl .one ByteRetirementTests.rmwCandidate (fun _ => []) (.arrival AtomicMemoryTests.event)
      ByteContentsTests.initialState = .error (.authority .unready) := by
  apply ByteContents.finishControl_unready
  intro hr
  have hp := hr.1
  change false = true at hp
  cases hp

theorem real_fence_precedes_mma_arrival (a b) (tile : Fin 3) (lane : Wgmma.Lane) :
    Unified.ControlEdge HopperStage.block (candidate a b) (retryHistories (family a b))
      (.base (.source ((family a b).nativeId tile lane 0))) (node a b tile lane 1) := by
  apply Unified.native_arrival_edge
  · refine ⟨?_,?_,rfl,?_⟩
    · exact (Unified.view_present_iff _ _).mpr (Unified.native_signature_present
        (retry_actual_native_signature (family a b) (source a b) tile tile.isLt lane 0))
    · exact (Unified.view_present_iff _ _).mpr (Unified.native_signature_present
        (retry_actual_native_signature (family a b) (source a b) tile tile.isLt lane 1))
    · dsimp [ReplySourceFamily.nativeId]
      omega
  · rw [retry_actual_native_signature (family a b) (source a b) tile tile.isLt lane 1]
    rfl

theorem actual_mma_arrival_rejects_missing_fence (a b) (tile : Fin 3) (lane : Wgmma.Lane) :
    ByteContents.finishControl HopperStage.block (candidate a b) (retryHistories (family a b)) (node a b tile lane 1)
      {state a b tile lane 1 with coupled := ⟨Ptx.Async.initial 0 [],fun _ => False⟩} = .error (.authority .unready) := by
  apply ByteContents.finishControl_unready
  intro hr
  exact hr.2.2 _ (real_fence_precedes_mma_arrival a b tile lane)

theorem control_completion_cannot_discard_held_fragment (a b) (tile : Fin 3) (lane : Wgmma.Lane) (index : Fin 4) :
    ∀ next, ByteContents.finishControl HopperStage.block (candidate a b) (retryHistories (family a b)) (node a b tile lane index)
      (heldState a b tile lane index) ≠ .ok next := by
  apply ByteContents.finishControl_rejects_held (k := ByteAuthority.key spare) (mode := .read)
  change get? (Iris.Std.PartialMap.map ByteContents.Payload.owner (insert _ _ _)) _ = _
  rw [get?_map,get?_insert]
  rfl

end
end Ptx.ByteContentsControlTests
