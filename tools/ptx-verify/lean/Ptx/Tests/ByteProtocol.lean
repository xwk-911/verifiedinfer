import Ptx.Kernels.HopperDoubleBufferByteProtocol
import Ptx.Tests.ByteExecution

/-! Real RMW source-completion guards, exact protocol errors and native
source/device/acquire composition over the existing actual Hopper family.
No protocol scalar cell is equated with physical GPU byte contents.
-/
namespace Ptx.ByteProtocolTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
open Ptx.ByteRetirementTests Ptx.ByteAcquisitionTests Ptx.ByteExecutionTests
noncomputable section

def prepareActions : List Ptx.Async.Action := [.access 0 0 .write,.record 0 0]
def prepared : Ptx.Async.State := (Ptx.Async.run (Ptx.Async.initial 1 [7]) prepareActions).toOption.getD (Ptx.Async.initial 1 [7])
def afterDevice : Ptx.Async.State := (Ptx.Async.deviceStep prepared 0).toOption.getD prepared
def afterAcquire : Ptx.Async.State := (Ptx.Async.await afterDevice 0).toOption.getD afterDevice
def afterDeviceState : ByteAuthority.State := ⟨⟨afterDevice,Present rmwCandidate⟩,ByteAuthority.Footprint.pool rmwDemands⟩
def plan : Bridge.Plan := fun ticket => if ticket = ⟨0,1⟩ then some .kernel else none
def ctx : ByteAuthorityHeap.Context := {block := .one,candidate := rmwCandidate,histories := fun _ => [],plan := plan}
def state (done : Cut) : ByteAuthority.State := ⟨⟨prepared,done⟩,ByteAuthority.Footprint.pool rmwDemands⟩
def stream : Ptx.Async.Stream := ⟨1,0,[.access 0 .write],[]⟩

theorem preparation_is_an_actual_public_run : Ptx.Async.run (Ptx.Async.initial 1 [7]) prepareActions = .ok prepared := by decide
theorem prepared_stream_lookup : Ptx.Async.getStream prepared 0 = .ok stream := by decide
theorem fifo_step_is_ready_before_source_finishes : Ptx.Async.deviceStep prepared 0 = .ok afterDevice := by decide
theorem protocol_finishes_only_after_device_and_acquire :
    Ptx.Async.run prepared [.device 0,.acquire 0] = .ok afterAcquire := by decide
theorem device_completion_alone_keeps_the_loan : (afterDevice.buffers[0]?.map (fun buffer => buffer.loans.length)) = some 1 := by decide
theorem final_acquire_returns_the_loan : (afterAcquire.buffers[0]?.map (fun buffer => buffer.loans.length)) = some 0 := by decide

theorem next_work_is_not_complete_before_actual_source :
    ¬ByteAuthority.NextCompleted rmwCandidate (fun _ => []) ctx.cluster plan (fun _ => False) 0 stream := by
  intro hc
  have hk := hc .kernel (by simp [plan,stream])
  cases hk with
  | kernel _ hd => exact hd rmwNode rmw_ready_from_empty.1

theorem device_cannot_fabricate_source_completion :
    ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan (.device 0) (state (fun _ => False)) =
      .error .incompleteWork :=
  ByteAuthority.execute_device_uncompleted prepared_stream_lookup fifo_step_is_ready_before_source_finishes
    next_work_is_not_complete_before_actual_source

theorem native_script_rejects_uncompleted_source :
    IrisExecution.run (ByteAuthorityHeap.transition ctx) (ByteAuthorityHeap.protocolActions [.device 0]) (state (fun _ => False)) =
      .error .incompleteWork := by
  change (ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan (.device 0) (state (fun _ => False))).bind _ = _
  rw [device_cannot_fabricate_source_completion]
  rfl

theorem rejected_device_preserves_controller_and_frames [ByteAuthorityHeap.GS] (frame : IProp ByteAuthorityHeap.GF) :
    ByteAuthorityHeap.control (state (fun _ => False)) ∗ frame ⊢
      WP (ByteAuthorityHeap.script ctx (ByteAuthorityHeap.protocolActions [.device 0]))
      {{ value, ⌜value = .error .incompleteWork⌝ ∗ ByteAuthorityHeap.control (state (fun _ => False)) ∗ frame }} :=
  ByteAuthorityHeap.script_reject_wp ctx _ (.protocol (.device 0)) [] .incompleteWork frame device_cannot_fabricate_source_completion

theorem all_mapped_work_complete_at_actual_complete_cut :
    Bridge.AllCompleted Tma.localShared ctx.candidate ctx.histories ctx.cluster ctx.plan (Present rmwCandidate) := by
  intro ticket work hm
  change (if ticket = ⟨0,1⟩ then some Work.kernel else none) = some work at hm
  split at hm
  · cases hm
    exact .kernel actual_rmw_source_complete (fun _ h => h)
  · cases hm

theorem device_runs_after_source_completion :
    ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan (.device 0) (state (Present rmwCandidate)) =
      .ok ⟨⟨afterDevice,Present rmwCandidate⟩,ByteAuthority.Footprint.pool rmwDemands⟩ :=
  ByteAuthority.execute_device_success prepared_stream_lookup fifo_step_is_ready_before_source_finishes
    (fun work hm => all_mapped_work_complete_at_actual_complete_cut _ work hm)

theorem source_checked_protocol_run_returns_exact_state :
    IrisExecution.run (ByteAuthorityHeap.transition ctx) (ByteAuthorityHeap.protocolActions [.device 0,.host (.acquire 0)])
      (state (Present rmwCandidate)) = .ok ⟨⟨afterAcquire,Present rmwCandidate⟩,ByteAuthority.Footprint.pool rmwDemands⟩ :=
  ByteAuthorityHeap.completed_protocol_run ctx _ _ _ _ _ all_mapped_work_complete_at_actual_complete_cut protocol_finishes_only_after_device_and_acquire

theorem source_checked_protocol_closed_adequate :
    adequate .NotStuck (ByteAuthorityHeap.script ctx (ByteAuthorityHeap.protocolActions [.device 0,.host (.acquire 0)]))
      (state (Present rmwCandidate))
      (fun value _ => value = .ok (⟨⟨afterAcquire,Present rmwCandidate⟩,ByteAuthority.Footprint.pool rmwDemands⟩ : ByteAuthority.State)) := by
  apply ByteAuthorityHeap.protocol_adequate
  exact ByteAuthority.runCommands_succeeds all_mapped_work_complete_at_actual_complete_cut _ protocol_finishes_only_after_device_and_acquire _

theorem early_acquire_keeps_original_error :
    ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan (.host (.acquire 0)) (state (Present rmwCandidate)) =
      .error (.protocolFailure .notComplete) := ByteAuthority.execute_host_error (by decide)

theorem reclaim_before_acquire_keeps_original_error :
    ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan (.host (.reclaim 0))
      ⟨⟨afterDevice,Present rmwCandidate⟩,ByteAuthority.Footprint.pool rmwDemands⟩ =
      .error (.protocolFailure .outstandingLoan) := ByteAuthority.execute_host_error (by decide)

theorem write_before_acquire_keeps_original_error :
    ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan (.host (.write 0 99))
      ⟨⟨afterDevice,Present rmwCandidate⟩,ByteAuthority.Footprint.pool rmwDemands⟩ =
      .error (.protocolFailure .outstandingLoan) := ByteAuthority.execute_host_error (by decide)

theorem invalid_event_keeps_original_error :
    ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan (.host (.acquire 99)) (state (Present rmwCandidate)) =
      .error (.protocolFailure .invalidEvent) := ByteAuthority.execute_host_error (by decide)

theorem duplicate_record_keeps_original_error :
    ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan (.host (.record 0 0)) (state (Present rmwCandidate)) =
      .error (.protocolFailure .duplicateEvent) := ByteAuthority.execute_host_error (by decide)

theorem empty_queue_keeps_original_error :
    ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan (.device 0)
      ⟨⟨afterDevice,Present rmwCandidate⟩,ByteAuthority.Footprint.pool rmwDemands⟩ =
      .error (.protocolFailure .emptyQueue) :=
  ByteAuthority.execute_device_error (st := ⟨1,1,[],[]⟩) (by decide) (by decide)

theorem final_acquire_allows_reclaim : ∃ protocol, Ptx.Async.reclaim afterAcquire 0 = .ok protocol :=
  ⟨(Ptx.Async.reclaim afterAcquire 0).toOption.getD afterAcquire,by decide⟩
theorem final_acquire_allows_reuse : ∃ protocol, Ptx.Async.hostWrite afterAcquire 0 99 = .ok protocol :=
  ⟨(Ptx.Async.hostWrite afterAcquire 0 99).toOption.getD afterAcquire,by decide⟩

theorem successful_commands_preserve_byte_authority_and_source_cut (context : ByteAuthorityHeap.Context)
    (command : Bridge.Command) (before after : ByteAuthority.State)
    (hr : ByteAuthority.executeCommand context.candidate context.histories context.cluster context.plan command before = .ok after) :
    after.coupled.done = before.coupled.done ∧ after.bytes = before.bytes :=
  (ByteAuthority.executeCommand_spec (block := context.block) hr).2

theorem complete_native_hopper_pipeline_exists (a b tiles schedules) (frame : Location → Symbolic.Byte)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∃ nodes, ByteAuthority.Footprint.Ordered HopperStage.block (retryDataCandidate a b tiles schedules)
        (retryHistories (retryDataFamily a b tiles schedules)) (fun _ => False) nodes (Present (retryDataCandidate a b tiles schedules)) ∧
      IrisExecution.run (ByteAuthorityHeap.transition (Whole.byteContext (retryDataFamily a b tiles schedules)))
        (Whole.bytePipelineActions (retryDataFamily a b tiles schedules) nodes)
        (ByteAuthority.Footprint.initialized ⟨Whole.prepared HopperWholePlanTests.values tiles,fun _ => False⟩ (Whole.byteLocations (retryDataFamily a b tiles schedules))) =
        .ok (ByteAuthority.Footprint.initialized ⟨Whole.returned HopperWholePlanTests.values tiles,Present (retryDataCandidate a b tiles schedules)⟩
          (Whole.byteLocations (retryDataFamily a b tiles schedules))) ∧
      adequate .NotStuck
        (ByteAuthorityHeap.script (Whole.byteContext (retryDataFamily a b tiles schedules))
          (Whole.bytePipelineActions (retryDataFamily a b tiles schedules) nodes))
        (ByteAuthority.Footprint.initialized ⟨Whole.prepared HopperWholePlanTests.values tiles,fun _ => False⟩ (Whole.byteLocations (retryDataFamily a b tiles schedules)))
        (fun value _ => value = .ok (ByteAuthority.Footprint.initialized ⟨Whole.returned HopperWholePlanTests.values tiles,Present (retryDataCandidate a b tiles schedules)⟩
          (Whole.byteLocations (retryDataFamily a b tiles schedules)))) :=
  Whole.complete_byte_pipeline_witness _ ht hb (retry_data_complete_components a b tiles schedules frame ht hb).1 _ rfl

theorem omitted_final_device_step_is_rejected_in_native_script (a b schedules) (frame : Location → Symbolic.Byte) :
    IrisExecution.run (ByteAuthorityHeap.transition (Whole.byteContext (retryDataFamily a b 4 schedules)))
      (ByteAuthorityHeap.protocolActions (List.replicate 25 (.device 0) ++ [.host (.acquire 0)]))
      (ByteAuthority.Footprint.initialized ⟨Whole.prepared HopperWholePlanTests.values 4,Present (retryDataCandidate a b 4 schedules)⟩
        (Whole.byteLocations (retryDataFamily a b 4 schedules))) = .error (.protocolFailure .notComplete) := by
  have htma := (retry_data_complete_components a b 4 schedules frame (by decide) (by decide)).1
  apply ByteAuthorityHeap.completed_protocol_error
  · exact Whole.plan_full_completed _ (by decide) (by decide) htma
  · exact HopperWholePlanTests.one_missing_root_device_step_rejected

theorem invalid_stream_keeps_original_error :
    ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan (.device 99) (state (Present rmwCandidate)) =
      .error (.protocolFailure .invalidStream) := ByteAuthority.executeCommand_protocol_error (by decide)

def waitPreparation : List Ptx.Async.Action := [.access 0 0 .write,.record 0 0,.wait 1 0]
def waiting : Ptx.Async.State := (Ptx.Async.run (Ptx.Async.initial 2 [7]) waitPreparation).toOption.getD (Ptx.Async.initial 2 [7])
def waitingState : ByteAuthority.State := ⟨⟨waiting,Present rmwCandidate⟩,ByteAuthority.Footprint.pool rmwDemands⟩
def waitFinished : Ptx.Async.State := (Ptx.Async.run waiting [.device 0,.device 1,.acquire 0]).toOption.getD waiting

theorem cross_stream_wait_has_real_public_preparation :
    Ptx.Async.run (Ptx.Async.initial 2 [7]) waitPreparation = .ok waiting := by decide

theorem complete_source_does_not_bypass_queued_stream_wait :
    ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan (.device 1)
      ⟨⟨waiting,Present rmwCandidate⟩,ByteAuthority.Footprint.pool rmwDemands⟩ = .error (.protocolFailure .notComplete) :=
  ByteAuthority.executeCommand_protocol_error (by decide)

theorem native_cross_stream_wait_runs_after_dependency_finishes :
    IrisExecution.run (ByteAuthorityHeap.transition ctx)
      (ByteAuthorityHeap.protocolActions [.device 0,.device 1,.host (.acquire 0)])
      ⟨⟨waiting,Present rmwCandidate⟩,ByteAuthority.Footprint.pool rmwDemands⟩ =
      .ok ⟨⟨waitFinished,Present rmwCandidate⟩,ByteAuthority.Footprint.pool rmwDemands⟩ :=
  ByteAuthorityHeap.completed_protocol_run ctx _ _ _ _ _ all_mapped_work_complete_at_actual_complete_cut (by decide)

end
end Ptx.ByteProtocolTests
