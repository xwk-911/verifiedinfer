import Ptx.Iris.ByteAuthority
import Ptx.Tests.HopperKernelOwnership

/-! Actual source mbarrier bytes, no fabricated memory values; active authority
cannot be duplicated, skipped on retirement or confused across CTA/space keys.
The claim WP uses the native GenHeap state interpretation, not OwnP framing.
-/
namespace Ptx.ByteAuthorityTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

abbrev candidate := zeroCandidate
abbrev source := HopperKernelOwnershipTests.zero_source_checked
abbrev complete := HopperKernelOwnershipTests.zero_source_complete

def node (slot : Stage) : Unified.ControlNode := .base (.source (dataInitId 0 slot))
def location (slot : Stage) (offset : Fin 8) := (dataGate slot).add offset.val
def request (slot : Stage) (offset : Fin 8) : ByteAuthority.Claim := ⟨node slot,location slot offset,.write⟩
def cut (slot : Stage) : Cut := fun n => Present candidate n ∧ dataNativeControlRank 0 n < dataNativeControlRank 0 (node slot)
def state (slot : Stage) (offset : Fin 8) : ByteAuthority.State :=
  ⟨⟨Ptx.Async.initial 0 [],cut slot⟩,insert Iris.Std.PartialMap.empty (ByteAuthority.key (location slot offset)) .available⟩
def claimed (slot : Stage) (offset : Fin 8) : ByteAuthority.State :=
  {state slot offset with bytes := insert (state slot offset).bytes (ByteAuthority.key (location slot offset)) (.held (node slot) .write)}
def ctx : ByteAuthorityHeap.Context := {block := HopperStage.block,candidate := candidate,histories := zeroHistories}

theorem actual_init_uses_storage (slot : Stage) (offset : Fin 8) : ByteAuthority.Uses candidate (node slot) (location slot offset) .write :=
  ⟨.kernel,.kernel (HopperKernelOwnershipTests.zero_initialization_uses_all_storage_bytes slot offset)⟩

theorem actual_rank_cut_is_reachable (slot : Stage) : Reached HopperStage.block candidate zeroHistories (cut slot) :=
  actual_rank_prefix_reached (completed_zero_history_valid source complete) (dataNativeControlRank 0)
    (fun _ _ => completed_zero_control_rank source complete) _

theorem actual_rank_cut_ready (slot : Stage) : ByteAuthority.Ready HopperStage.block candidate zeroHistories (cut slot) (node slot) :=
  ByteAuthority.ready_at_rank_cut (completed_zero_history_valid source complete) (dataNativeControlRank 0)
    (fun _ _ => completed_zero_control_rank source complete)
    (kernel_use_present (HopperKernelOwnershipTests.zero_initialization_uses_all_storage_bytes slot 0))

theorem actual_claim_succeeds (slot : Stage) (offset : Fin 8) :
    ByteAuthority.claim HopperStage.block candidate zeroHistories (request slot offset) (state slot offset) = .ok (claimed slot offset) :=
  ByteAuthority.claim_succeeds (actual_rank_cut_ready slot) (actual_init_uses_storage slot offset) (by simp [state,request,get?_insert])

theorem repeated_actual_write_claim_rejected (slot : Stage) (offset : Fin 8) :
    ByteAuthority.claim HopperStage.block candidate zeroHistories (request slot offset) (claimed slot offset) = .error .unavailable := by
  apply ByteAuthority.claim_unavailable (actual_rank_cut_ready slot) (actual_init_uses_storage slot offset)
  simp [claimed,request,get?_insert]

theorem missing_byte_authority_rejected (slot : Stage) (offset : Fin 8) :
    ByteAuthority.claim HopperStage.block candidate zeroHistories (request slot offset) {state slot offset with bytes := Iris.Std.PartialMap.empty} = .error .unavailable := by
  apply ByteAuthority.claim_unavailable (actual_rank_cut_ready slot) (actual_init_uses_storage slot offset)
  change (none : Option ByteAuthority.Owner) ≠ some .available
  decide

theorem same_address_global_shared_distinct :
    ByteAuthority.key ⟨.global,8⟩ ≠ ByteAuthority.key ⟨.shared .zero,8⟩ := by decide

theorem same_address_other_cta_distinct :
    ByteAuthority.key ⟨.shared .zero,8⟩ ≠ ByteAuthority.key ⟨.shared ⟨1,0,0⟩,8⟩ := by decide

theorem byte_authority_never_aliases_control (loc : Location) : ByteAuthority.key loc ≠ ByteAuthority.controlKey :=
  ByteAuthority.byte_key_not_control loc

theorem omitted_barrier_bytes_prevent_retirement : ¬ByteAuthority.AllHeld candidate (claimed 1 7) (node 1) := by
  intro hall
  have hu := actual_init_uses_storage 1 0
  obtain ⟨granted,hh,_⟩ := hall (location 1 0) .write hu
  have hne : location (1 : Stage) (7 : Fin 8) ≠ location (1 : Stage) (0 : Fin 8) := by decide
  rw [ByteAuthority.claim_other_byte_preserved (actual_claim_succeeds 1 7) hne] at hh
  have hk : ByteAuthority.key (location (1 : Stage) (7 : Fin 8)) ≠ ByteAuthority.key (location (1 : Stage) (0 : Fin 8)) :=
    fun he => hne (ByteAuthority.key_injective he)
  simp only [state,get?_insert_ne hk] at hh
  cases hh

theorem actual_retirement_returns_each_held_byte {state : ByteAuthority.State} (slot : Stage) (offset : Fin 8)
    (ha : ByteAuthority.AllHeld candidate state (node slot)) :
    get? (ByteAuthority.retired state (node slot)).bytes (ByteAuthority.key (location slot offset)) = some .available :=
  ByteAuthority.retire_returns_actual_byte ha (actual_init_uses_storage slot offset)

theorem retirement_is_actual_source_advance {state : ByteAuthority.State} (slot : Stage)
    (hr : ByteAuthority.Ready HopperStage.block candidate zeroHistories state.coupled.done (node slot)) :
    Bridge.Step HopperStage.block Tma.localShared candidate zeroHistories dataCluster (fun _ => none)
      state.coupled (ByteAuthority.retired state (node slot)).coupled := ByteAuthority.retire_projects hr

theorem no_cut_preserving_source_shortcut {before after : Cut}
    (ha : Advance HopperStage.block candidate zeroHistories before after) : before ≠ after := ByteAuthority.advance_changes_cut ha

theorem done_access_cannot_be_claimed {state : ByteAuthority.State} (slot : Stage) (offset : Fin 8)
    (hd : state.coupled.done (node slot)) :
    ByteAuthority.claim HopperStage.block candidate zeroHistories (request slot offset) state = .error .unready :=
  ByteAuthority.claim_done_rejected hd

theorem resource_storage_read_claim_has_no_source_use (slot : Stage) (offset : Fin 8) :
    ¬ByteAuthority.Uses candidate (node slot) (location slot offset) .read := by
  have hn : ∀ (control : Unified.ControlNode) (loc : Location), KernelUse Tma.localShared candidate control loc .read → False := by
    intro control loc hu
    cases hu with
    | @read id kind loc value he hb =>
      have hx := candidate_ordinary_read_none (by decide) source complete id loc
      simp [Access.readByte,Access.kind,he,hb] at hx
  intro ⟨work,hu⟩
  cases hu with
  | async hu => cases hu
  | kernel hu => exact hn _ _ hu

theorem wrong_resource_storage_mode_rejected (slot : Stage) (offset : Fin 8) :
    ByteAuthority.claim HopperStage.block candidate zeroHistories {request slot offset with mode := .read} (state slot offset) =
      .error .uncovered := by
  have hr : ByteAuthority.Ready HopperStage.block candidate zeroHistories (state slot offset).coupled.done (node slot) := actual_rank_cut_ready slot
  have hu := resource_storage_read_claim_has_no_source_use slot offset
  simp only [ByteAuthority.claim,request,hr,hu,ite_true,ite_false]

theorem source_byte_claim_has_iris_wp [ByteAuthorityHeap.GS] (slot : Stage) (offset : Fin 8) :
    ByteAuthorityHeap.control (state slot offset) ∗ ByteAuthorityHeap.byte (location slot offset) (.own 1) .available ⊢
      WP (ByteAuthorityHeap.invoke ctx (request slot offset))
        {{ value, ⌜∃ next, value = .ok next⌝ ∗ ByteAuthorityHeap.control (claimed slot offset) ∗
          ByteAuthorityHeap.byte (location slot offset) (.own 1) (.held (node slot) .write) }} :=
  ByteAuthorityHeap.claim_local_wp ctx (state slot offset) (request slot offset) (actual_rank_cut_ready slot) (actual_init_uses_storage slot offset)

theorem source_byte_claim_closed_adequate (slot : Stage) (offset : Fin 8) :
    adequate .NotStuck (ByteAuthorityHeap.invoke ctx (request slot offset)) (state slot offset)
      (fun result _ => ∃ next, result = .ok next) :=
  ByteAuthorityHeap.claim_adequate ctx (state slot offset) (request slot offset) (actual_rank_cut_ready slot)
    (actual_init_uses_storage slot offset) (by simp [state,request,get?_insert])

theorem duplicated_full_byte_authority_rejected [ByteAuthorityHeap.GS] (loc : Location) (a b : ByteAuthority.Owner) :
    ByteAuthorityHeap.byte loc (.own 1) a ∗ ByteAuthorityHeap.byte loc (.own 1) b ⊢ False :=
  ByteAuthorityHeap.byte_full_exclusive loc a b

theorem shared_fraction_is_same_byte_authority [ByteAuthorityHeap.GS] (loc : Location) (q : Qp) (owner : ByteAuthority.Owner) :
    ByteAuthorityHeap.byte loc (.own q) owner ⊣⊢
      ByteAuthorityHeap.byte loc (.own q.half) owner ∗ ByteAuthorityHeap.byte loc (.own q.half) owner := ByteAuthorityHeap.byte_split loc q owner

end
end Ptx.ByteAuthorityTests
