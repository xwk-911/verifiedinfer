import Ptx.Kernels.HopperDoubleBufferValueProtocol
import Ptx.Tests.ByteContents
import Ptx.Tests.ByteProtocol
import Ptx.Tests.HopperValueExecution

/-! Checked command errors and real RMW contents, plus the complete nonzero
Hopper source/value/device/acquire execution. Protocol scalar buffers and
physical GPU bytes remain distinct. No new GPU execution is asserted.
-/
namespace Ptx.ByteContentsProtocolTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
open Ptx.ByteRetirementTests Ptx.ByteExecutionTests
noncomputable section

def ctx : ByteContentsProtocolHeap.Context :=
  ⟨ByteContentsTests.ctx,ByteProtocolTests.ctx.cluster,ByteProtocolTests.plan⟩
def state (done : Cut) : ByteContents.State :=
  ⟨⟨ByteProtocolTests.prepared,done⟩,ByteContentsTests.finalState.cells⟩
def afterDevice := ByteContents.withCoupled (state (Present rmwCandidate)) ⟨ByteProtocolTests.afterDevice,Present rmwCandidate⟩
def afterAcquire := ByteContents.withCoupled (state (Present rmwCandidate)) ⟨ByteProtocolTests.afterAcquire,Present rmwCandidate⟩
def commands : List Bridge.Command := [.device 0,.host (.acquire 0)]

theorem original_fifo_is_ready_while_actual_source_is_not :
    Ptx.Async.deviceStep (state (fun _ => False)).coupled.protocol 0 = .ok ByteProtocolTests.afterDevice :=
  ByteProtocolTests.fifo_step_is_ready_before_source_finishes

theorem value_device_cannot_fabricate_actual_source_completion :
    ByteContentsProtocolHeap.transition ctx (.protocol (.device 0)) (state (fun _ => False)) = .error (.authority .incompleteWork) := by
  apply ByteContentsProtocolHeap.protocol_error
  exact ByteAuthority.execute_device_uncompleted ByteProtocolTests.prepared_stream_lookup
    ByteProtocolTests.fifo_step_is_ready_before_source_finishes ByteProtocolTests.next_work_is_not_complete_before_actual_source

theorem actual_completed_source_allows_device_command :
    ByteContentsProtocolHeap.transition ctx (.protocol (.device 0)) (state (Present rmwCandidate)) = .ok afterDevice := by
  apply ByteContents.executeCommand_success (authority := ByteContents.erase afterDevice)
  exact ByteAuthority.execute_device_success ByteProtocolTests.prepared_stream_lookup
    ByteProtocolTests.fifo_step_is_ready_before_source_finishes
    (fun work hm => ByteProtocolTests.all_mapped_work_complete_at_actual_complete_cut _ work hm)

theorem completed_protocol_has_actual_value_state_run :
    IrisExecution.run (ByteContentsProtocolHeap.transition ctx) (ByteContentsProtocolHeap.protocolActions commands)
      (state (Present rmwCandidate)) = .ok afterAcquire :=
  ByteContentsProtocolHeap.completed_protocol_run ctx commands _ _ ByteProtocolTests.all_mapped_work_complete_at_actual_complete_cut
    ByteProtocolTests.protocol_finishes_only_after_device_and_acquire

theorem actual_final_rmw_counter_is_still_one :
    ByteContents.valueAt afterAcquire AtomicMemoryTests.base = some (.bits (byte 1)) := by
  have hg := ByteContentsTests.final_value_cell_has_returned_authority (0 : Fin 4)
  change get? afterAcquire.cells (ByteAuthority.key AtomicMemoryTests.base) = some ⟨.available,some (.bits (byte 1))⟩ at hg
  unfold ByteContents.valueAt
  rw [hg]
  rfl

theorem every_actual_counter_byte_is_preserved : afterAcquire.cells = (state (Present rmwCandidate)).cells :=
  (ByteContentsProtocolHeap.protocol_preserves_cells_and_cut ctx commands completed_protocol_has_actual_value_state_run).1

theorem device_step_keeps_original_loan : (afterDevice.coupled.protocol.buffers[0]?.map (fun buffer => buffer.loans.length)) = some 1 := by decide
theorem acquire_returns_original_loan : (afterAcquire.coupled.protocol.buffers[0]?.map (fun buffer => buffer.loans.length)) = some 0 := by decide

theorem source_done_does_not_make_early_acquire_valid :
    ByteContentsProtocolHeap.transition ctx (.protocol (.host (.acquire 0))) (state (Present rmwCandidate)) =
      .error (.authority (.protocolFailure .notComplete)) := by
  apply ByteContentsProtocolHeap.protocol_error
  exact ByteAuthority.execute_host_error (by decide)

theorem device_done_does_not_allow_early_reclaim :
    ByteContentsProtocolHeap.transition ctx (.protocol (.host (.reclaim 0))) afterDevice =
      .error (.authority (.protocolFailure .outstandingLoan)) := by
  apply ByteContentsProtocolHeap.protocol_error
  exact ByteAuthority.execute_host_error (by decide)

theorem device_done_does_not_allow_early_write :
    ByteContentsProtocolHeap.transition ctx (.protocol (.host (.write 0 99))) afterDevice =
      .error (.authority (.protocolFailure .outstandingLoan)) := by
  apply ByteContentsProtocolHeap.protocol_error
  exact ByteAuthority.execute_host_error (by decide)

theorem second_device_completion_keeps_original_empty_queue_error :
    ByteContentsProtocolHeap.transition ctx (.protocol (.device 0)) afterAcquire = .error (.authority (.protocolFailure .emptyQueue)) := by
  apply ByteContentsProtocolHeap.protocol_error
  exact ByteAuthority.execute_device_error (st := ⟨1,1,[],[]⟩) (by decide) (by decide)

theorem wrapped_source_finish_still_checks_real_values :
    ByteContentsProtocolHeap.transition ctx (.source (.finish ByteContentsTests.memoryNode Ptx.ByteRetirementTests.rmwDemands)) ByteContentsTests.wrongReadState =
      .error .readMismatch := ByteContentsTests.wrong_data_is_rejected_despite_full_authority

theorem returned_protocol_has_native_closed_adequacy :
    adequate .NotStuck (ByteContentsProtocolHeap.script ctx (ByteContentsProtocolHeap.protocolActions commands))
      (state (Present rmwCandidate)) (fun result _ => result = .ok afterAcquire) :=
  ByteContentsProtocolHeap.script_adequate ctx _ _ _ completed_protocol_has_actual_value_state_run

theorem native_device_rule_frames_real_fractional_counter [ByteContentsHeap.GS] :
    ByteContentsHeap.control (state (Present rmwCandidate)) ∗
      ByteContentsHeap.byte AtomicMemoryTests.base (.own (1 : Qp).half) ⟨.available,some (.bits (byte 1))⟩ ⊢
      WP (ByteContentsProtocolHeap.script ctx [.protocol (.device 0)])
      {{ result, ⌜result = .ok afterDevice⌝ ∗ ByteContentsHeap.control afterDevice ∗
        ByteContentsHeap.byte AtomicMemoryTests.base (.own (1 : Qp).half) ⟨.available,some (.bits (byte 1))⟩ }} :=
  ByteContentsProtocolHeap.protocol_local_wp ctx (.device 0) _ _ _ actual_completed_source_allows_device_command

theorem native_early_acquire_rejection_preserves_real_fractional_counter [ByteContentsHeap.GS] :
    ByteContentsHeap.control (state (Present rmwCandidate)) ∗
      ByteContentsHeap.byte AtomicMemoryTests.base (.own (1 : Qp).half) ⟨.available,some (.bits (byte 1))⟩ ⊢
      WP (ByteContentsProtocolHeap.script ctx [.protocol (.host (.acquire 0))])
      {{ result, ⌜result = .error (.authority (.protocolFailure .notComplete))⌝ ∗
        ByteContentsHeap.control (state (Present rmwCandidate)) ∗
        ByteContentsHeap.byte AtomicMemoryTests.base (.own (1 : Qp).half) ⟨.available,some (.bits (byte 1))⟩ }} :=
  ByteContentsMachine.script_reject_wp (ByteContentsProtocolHeap.transition ctx) _ (.protocol (.host (.acquire 0))) []
    (.authority (.protocolFailure .notComplete)) _ source_done_does_not_make_early_acquire_valid

def values : List Nat := List.range 10
abbrev schedule := HopperRetryDataTests.schedule
abbrev frame := HopperRetryDataTests.frame
abbrev family := HopperRetryDataTests.family

theorem preparation_is_still_an_actual_public_interpreter_run :
    Ptx.Async.run (Ptx.Async.initial 1 values) (Whole.prepareActions 3) = .ok (Whole.prepared values 3) :=
  Whole.preparation_succeeds values (by decide) 3

theorem complete_hopper_value_protocol_execution_exists (a b) :
    ∃ actions final,
      IrisExecution.run (ByteContentsProtocolHeap.transition (valueProtocolContext (family a b))) (valuePipelineActions 3 actions)
        (retryValueInitialState a b 3 schedule frame (Whole.prepared values 3)) = .ok final ∧
      final.coupled = ⟨Whole.returned values 3,Present (retryDataCandidate a b 3 schedule)⟩ ∧
      Ptx.Async.Drain.Returned final.coupled.protocol ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4), ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
        some (.realPart .f32 (specification a b 3 (Wgmma.cCoord (lane,slot))) index.val)) ∧
      adequate .NotStuck (ByteContentsProtocolHeap.script (valueProtocolContext (family a b)) (valuePipelineActions 3 actions))
        (retryValueInitialState a b 3 schedule frame (Whole.prepared values 3)) (fun result _ => result = .ok final) := by
  obtain ⟨actions,final,hr,hc,ha,hreturned,hlive,hm,hreuse,hadequate,hproject⟩ := retry_data_value_pipeline_witness a b 3 schedule frame values (by decide) (by decide) (by decide)
  exact ⟨actions,final,hr,hc,hreturned,hm,hadequate⟩

theorem arbitrary_successful_interleavings_keep_correct_matrix (a b protocol actions final)
    (hr : IrisExecution.run (ByteContentsProtocolHeap.transition (valueProtocolContext (family a b))) actions
      (retryValueInitialState a b 3 schedule frame protocol) = .ok final)
    (hc : final.coupled.done = Present (retryDataCandidate a b 3 schedule)) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      some (.realPart .f32 (specification a b 3 (Wgmma.cCoord (lane,slot))) index.val) :=
  retry_data_value_protocol_output_of_run (by decide) (by decide) hr hc lane slot index

theorem nonzero_hopper_matrix_and_all_ten_returns_coexist :
    ∃ actions final,
      IrisExecution.run (ByteContentsProtocolHeap.transition (valueProtocolContext (family (fun _ _ => 1) (fun _ _ => 2)))) (valuePipelineActions 3 actions)
        (retryValueInitialState (fun _ _ => 1) (fun _ _ => 2) 3 schedule frame (Whole.prepared values 3)) = .ok final ∧
      Ptx.Async.Drain.Returned final.coupled.protocol ∧ ByteContentsHeap.Available final ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4), ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 96 index.val)) ∧
      (∀ bid, bid < 10 → (∃ next, Ptx.Async.reclaim final.coupled.protocol bid = .ok next) ∧
        ∀ value, ∃ next, Ptx.Async.hostWrite final.coupled.protocol bid value = .ok next) ∧
      adequate .NotStuck (ByteContentsProtocolHeap.script (valueProtocolContext (family (fun _ _ => 1) (fun _ _ => 2))) (valuePipelineActions 3 actions))
        (retryValueInitialState (fun _ _ => 1) (fun _ _ => 2) 3 schedule frame (Whole.prepared values 3)) (fun result _ => result = .ok final) := by
  obtain ⟨actions,final,hr,hc,ha,hreturned,hlive,hm,hreuse,hadequate,hproject⟩ := retry_data_value_pipeline_witness (fun _ _ => 1) (fun _ _ => 2) 3 schedule frame values (by decide) (by decide) (by decide)
  refine ⟨actions,final,hr,hreturned,ha,?_,hreuse,hadequate⟩
  intro lane slot index
  have hs := HopperRetryDataTests.nonzero_three_tile_accumulation lane slot
  rw [retry_data_final_accumulation] at hs
  rw [hm lane slot index,hs]

end
end Ptx.ByteContentsProtocolTests
