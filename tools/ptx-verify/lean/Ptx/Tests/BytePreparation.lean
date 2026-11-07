import Ptx.Kernels.HopperDoubleBufferPublicValues
import Ptx.Tests.ByteContentsProtocol

/-! Actual public preparation with initial no-loan state, exact queue sealing,
source-access gates, fractional real-byte framing and full nonzero Hopper
client execution. Protocol buffers remain distinct from physical GPU bytes.
-/
namespace Ptx.BytePreparationTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
open Ptx.ByteRetirementTests
noncomputable section

def ctx : ByteContentsPreparation.Context := ⟨ByteContentsProtocolTests.ctx,[.access 0 .write],0⟩
def initial : ByteContents.State :=
  ⟨⟨Ptx.Async.initial 1 [7],fun _ => False⟩,ByteContentsTests.initialState.cells⟩
def issued : Ptx.Async.State := (Ptx.Async.step (Ptx.Async.initial 1 [7]) (.access 0 0 .write)).toOption.getD (Ptx.Async.initial 1 [7])
def afterRequest := ByteContents.withCoupled initial ⟨issued,fun _ => False⟩
def prepared := ByteContents.withCoupled initial ⟨ByteProtocolTests.prepared,fun _ => False⟩
def prepareActions : List ByteContentsPreparation.Action := [.request (.access 0 .write),.seal]

theorem initial_protocol_has_no_loans : (initial.coupled.protocol.buffers[0]?.map (fun b => b.loans.length)) = some 0 := by decide
theorem actual_initial_pool_is_available : ByteContentsHeap.Available initial := ByteContentsHeap.initial_cells_available _ _ _
theorem actual_initial_state_can_prepare : ByteContentsPreparation.CanPrepare ctx initial :=
  ⟨⟨fun _ h => h,actual_initial_pool_is_available⟩,rfl⟩
theorem original_request_is_a_public_interpreter_step : Ptx.Async.step initial.coupled.protocol (.access 0 0 .write) = .ok issued := by decide

theorem native_request_submits_the_real_borrow :
    ByteContentsPreparation.transition ctx (.request (.access 0 .write)) initial = .ok afterRequest :=
  ByteContentsPreparation.request_success actual_initial_state_can_prepare original_request_is_a_public_interpreter_step

theorem submitted_request_has_exact_queue_and_ready_loans : Ptx.Async.Preparation.Ready issued [.access 0 .write] := by
  obtain ⟨protocol,hs,hr,_⟩ := Ptx.Async.Preparation.ready_access (bid := 0) .write (Ptx.Async.Preparation.ready_initial [7]) (by decide)
  have he : protocol = issued := Except.ok.inj (hs.symm.trans original_request_is_a_public_interpreter_step)
  simpa only [he,List.nil_append] using hr

theorem after_request_can_still_prepare : ByteContentsPreparation.CanPrepare ctx afterRequest :=
  ⟨⟨fun _ h => h,actual_initial_pool_is_available⟩,by decide⟩

theorem exact_queue_can_be_sealed : ByteContentsPreparation.transition ctx .seal afterRequest = .ok prepared :=
  ByteContentsPreparation.seal_success after_request_can_still_prepare submitted_request_has_exact_queue_and_ready_loans (by decide)

theorem recorded_exact_frontier_enables_execution : ByteContentsPreparation.Enabled ctx prepared := by
  unfold ByteContentsPreparation.Enabled
  decide

theorem native_public_preparation_runs_from_initial_no_loans :
    IrisExecution.run (ByteContentsPreparation.transition ctx) prepareActions initial = .ok prepared := by
  change (ByteContentsPreparation.transition ctx (.request (.access 0 .write)) initial).bind _ = _
  rw [native_request_submits_the_real_borrow]
  change (ByteContentsPreparation.transition ctx .seal afterRequest).bind _ = _
  rw [exact_queue_can_be_sealed]
  rfl

theorem original_record_would_accept_an_incomplete_frontier :
    ∃ protocol, Ptx.Async.step initial.coupled.protocol (.record 0 0) = .ok protocol :=
  ⟨(Ptx.Async.step initial.coupled.protocol (.record 0 0)).toOption.getD initial.coupled.protocol,by decide⟩

theorem native_seal_rejects_that_incomplete_queue : ByteContentsPreparation.transition ctx .seal initial = .error .preparationNotReady := by
  apply ByteContentsPreparation.seal_incomplete actual_initial_state_can_prepare
  intro hr
  have hn : initial.coupled.protocol.streams ≠ [⟨1,0,[.access 0 .write],[]⟩] := by decide
  exact hn hr.1

theorem claim_before_preparation_is_rejected :
    ByteContentsPreparation.transition ctx (.execute (.source (.claim (ByteContentsTests.request 0)))) initial = .error .unprepared :=
  ByteContentsPreparation.execution_unprepared (fun he => ByteContentsPreparation.enabled_not_preparable he actual_initial_state_can_prepare)

theorem device_before_preparation_is_rejected :
    ByteContentsPreparation.transition ctx (.execute (.protocol (.device 0))) initial = .error .unprepared :=
  ByteContentsPreparation.execution_unprepared (fun he => ByteContentsPreparation.enabled_not_preparable he actual_initial_state_can_prepare)

theorem request_after_seal_is_rejected : ByteContentsPreparation.transition ctx (.request (.access 0 .write)) prepared = .error .preparationClosed :=
  ByteContentsPreparation.request_after_seal_rejected recorded_exact_frontier_enables_execution

theorem duplicate_seal_is_rejected : ByteContentsPreparation.transition ctx .seal prepared = .error .preparationClosed :=
  ByteContentsPreparation.seal_after_seal_rejected recorded_exact_frontier_enables_execution

theorem invalid_buffer_preserves_original_error :
    ByteContentsPreparation.transition ctx (.request (.access 9 .write)) initial = .error (.authority (.protocolFailure .invalidBuffer)) := by
  simp only [ByteContentsPreparation.transition,actual_initial_state_can_prepare,ite_true]
  exact ByteContentsPreparation.publicStep_error (by decide)

theorem aliased_copy_preserves_original_error :
    ByteContentsPreparation.transition ctx (.request (.copy 0 0)) initial = .error (.authority (.protocolFailure .alias)) := by
  simp only [ByteContentsPreparation.transition,actual_initial_state_can_prepare,ite_true]
  exact ByteContentsPreparation.publicStep_error (by decide)

def readIssued : Ptx.Async.State := (Ptx.Async.step (Ptx.Async.initial 1 [7]) (.access 0 0 .read)).toOption.getD (Ptx.Async.initial 1 [7])
def wrongMode := ByteContents.withCoupled initial ⟨readIssued,fun _ => False⟩
theorem matching_ticket_count_with_wrong_mode_cannot_seal :
    ByteContentsPreparation.transition ctx .seal wrongMode = .error .preparationNotReady := by
  apply ByteContentsPreparation.seal_incomplete
  · exact ⟨⟨fun _ h => h,actual_initial_pool_is_available⟩,by decide⟩
  · intro hr
    have hn : readIssued.streams ≠ [⟨1,0,[.access 0 .write],[]⟩] := by decide
    exact hn hr.1

def started := ByteContents.withCoupled ByteContentsTests.finalState ⟨initial.coupled.protocol,ByteContentsTests.finalState.coupled.done⟩
theorem preparation_cannot_extend_a_started_source :
    ByteContentsPreparation.transition ctx (.request (.access 0 .write)) started = .error .preparationClosed := by
  apply ByteContentsPreparation.request_closed
  intro hp
  exact hp.1.1 rmwNode ByteContentsTests.source_advances_after_atomic_value_update

def held := ByteContents.withCoupled (ByteContentsTests.acquiredState 1) ⟨initial.coupled.protocol,fun _ => False⟩
theorem preparation_cannot_extend_an_active_byte_claim :
    ByteContentsPreparation.transition ctx (.request (.access 0 .write)) held = .error .preparationClosed := by
  apply ByteContentsPreparation.request_closed
  intro hp
  have hg : get? held.cells (ByteAuthority.key AtomicMemoryTests.base) = some ⟨.held rmwNode .write,some (.bits (byte 0))⟩ := by
    simp [held,ByteContents.withCoupled,ByteContentsTests.acquiredState,ByteContents.claimed,ByteContentsTests.request,
      AtomicMemoryTests.base,Location.add,get?_insert]
  have hn := hp.1.2 _ _ hg
  cases hn

theorem preparation_keeps_the_actual_counter_cell :
    get? prepared.cells (ByteAuthority.key AtomicMemoryTests.base) = some ⟨.available,some (.bits (byte 0))⟩ := by
  exact ByteContents.initialCells_member (Ptx.ByteContentsTests.emitted_read_location_is_in_initial_pool (by rfl))

theorem native_request_frames_real_fractional_counter [ByteContentsHeap.GS] :
    ByteContentsHeap.control initial ∗ ByteContentsHeap.byte AtomicMemoryTests.base (.own (1 : Qp).half) ⟨.available,some (.bits (byte 0))⟩ ⊢
      WP (ByteContentsPreparation.script ctx [.request (.access 0 .write)])
      {{ result, ⌜result = .ok afterRequest⌝ ∗ ByteContentsHeap.control afterRequest ∗
        ByteContentsHeap.byte AtomicMemoryTests.base (.own (1 : Qp).half) ⟨.available,some (.bits (byte 0))⟩ }} :=
  ByteContentsPreparation.preparation_local_wp ctx _ _ _ _ trivial native_request_submits_the_real_borrow

theorem native_unprepared_rejection_frames_real_fractional_counter [ByteContentsHeap.GS] :
    ByteContentsHeap.control initial ∗ ByteContentsHeap.byte AtomicMemoryTests.base (.own (1 : Qp).half) ⟨.available,some (.bits (byte 0))⟩ ⊢
      WP (ByteContentsPreparation.script ctx [.execute (.source (.claim (ByteContentsTests.request 0)))])
      {{ result, ⌜result = .error .unprepared⌝ ∗ ByteContentsHeap.control initial ∗
        ByteContentsHeap.byte AtomicMemoryTests.base (.own (1 : Qp).half) ⟨.available,some (.bits (byte 0))⟩ }} :=
  ByteContentsMachine.script_reject_wp (ByteContentsPreparation.transition ctx) _ _ [] .unprepared _ claim_before_preparation_is_rejected

theorem native_preparation_has_closed_adequacy :
    adequate .NotStuck (ByteContentsPreparation.script ctx prepareActions) initial (fun result _ => result = .ok prepared) :=
  ByteContentsPreparation.script_adequate ctx _ _ _ native_public_preparation_runs_from_initial_no_loans

abbrev schedule := HopperRetryDataTests.schedule
abbrev frame := HopperRetryDataTests.frame
abbrev family := HopperRetryDataTests.family
abbrev values := ByteContentsProtocolTests.values

theorem actual_three_tile_native_preparation (a b) :
    IrisExecution.run (ByteContentsPreparation.transition (preparationContext (family a b))) (publicPreparationActions 3)
      (retryValueInitialState a b 3 schedule frame (Ptx.Async.initial 1 values)) =
      .ok (retryValueInitialState a b 3 schedule frame (Whole.prepared values 3)) :=
  (retry_data_native_preparation a b 3 schedule frame values (by decide)).1

theorem nonzero_matrix_and_returns_from_initial_no_loans :
    ∃ actions final,
      IrisExecution.run (ByteContentsPreparation.transition (preparationContext (family (fun _ _ => 1) (fun _ _ => 2)))) (publicValueActions 3 actions)
        (retryValueInitialState (fun _ _ => 1) (fun _ _ => 2) 3 schedule frame (Ptx.Async.initial 1 values)) = .ok final ∧
      Ptx.Async.Drain.Returned final.coupled.protocol ∧ ByteContentsHeap.Available final ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4), ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 96 index.val)) ∧
      adequate .NotStuck (ByteContentsPreparation.script (preparationContext (family (fun _ _ => 1) (fun _ _ => 2))) (publicValueActions 3 actions))
        (retryValueInitialState (fun _ _ => 1) (fun _ _ => 2) 3 schedule frame (Ptx.Async.initial 1 values)) (fun result _ => result = .ok final) := by
  obtain ⟨actions,final,hr,hc,ha,hreturned,hlive,hm,hreuse,hadequate⟩ := retry_data_public_value_witness (fun _ _ => 1) (fun _ _ => 2) 3 schedule frame values (by decide) (by decide) (by decide)
  refine ⟨actions,final,hr,hreturned,ha,?_,hadequate⟩
  intro lane slot index
  have hs := HopperRetryDataTests.nonzero_three_tile_accumulation lane slot
  rw [retry_data_final_accumulation] at hs
  rw [hm lane slot index,hs]

theorem any_successful_full_client_has_correct_matrix (a b actions final)
    (hr : IrisExecution.run (ByteContentsPreparation.transition (preparationContext (family a b))) actions
      (retryValueInitialState a b 3 schedule frame (Ptx.Async.initial 1 values)) = .ok final)
    (hc : final.coupled.done = Present (retryDataCandidate a b 3 schedule)) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      some (.realPart .f32 (specification a b 3 (Wgmma.cCoord (lane,slot))) index.val) :=
  retry_data_public_value_output_of_run (by decide) (by decide) hr hc lane slot index

end
end Ptx.BytePreparationTests
