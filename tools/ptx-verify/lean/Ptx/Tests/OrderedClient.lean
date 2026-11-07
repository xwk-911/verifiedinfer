import Ptx.Kernels.ReleaseAcquireMessageClient
import Ptx.Tests.OrderedLoop

/-! Actual PTX acquire vs host completion/loan return. Even after a successful
source acquire, and again after all source threads exit, outstanding loans still
reject reclaim. Closed Iris rejection prevents error returns counting as success.
-/
namespace Ptx.OrderedClientTests
open Ptx.ISA Ptx.Kernels.ReleaseAcquireMessage
open Iris Iris.ProgramLogic
noncomputable section

def afterAcquire (value : Nat) : Ordered.Client.State :=
  ⟨⟨[trace 0 9,trace 1 7]⟩,Async.Contracts.deferredIssued value⟩
def atAcquire (value : Nat) : Ordered.Client.State :=
  ⟨⟨[trace 0 9,trace 1 6]⟩,Async.Contracts.deferredIssued value⟩

theorem actual_acquire_step (value : Nat) :
    Ordered.Client.step code launch (.source 1) (atAcquire value) = .ok (afterAcquire value) := rfl

theorem actual_acquire_tag_retained (value : Nat) :
    ((afterAcquire value).source.kindAt flagRead).map Ordered.Kind.order = some .acquire := rfl

theorem acquire_does_not_return_the_pending_loan (value : Nat) :
    (afterAcquire value).protocol.buffers[0]? =
      some {value := value,loans := [⟨⟨0,1⟩,.read⟩]} := rfl

theorem device_cannot_complete_at_acquire (value : Nat) :
    Ordered.Client.step code launch (.protocol (.device 0)) (afterAcquire value) = .error .sourceIncomplete := rfl

def producerReturnPending (value : Nat) : Ordered.Client.State :=
  ⟨⟨[trace 0 8,trace 1 12]⟩,Async.Contracts.deferredIssued value⟩

theorem pending_producer_is_an_actual_source_prefix : Ordered.Produced code bindings block (trace 0 8) := rfl

theorem consumer_exit_is_not_whole_launch_completion (value : Nat) :
    ((producerReturnPending value).source.traces[1]'(by simp [producerReturnPending])).final.core.thread.status = .done ∧
    Ordered.Client.step code launch (.protocol (.device 0)) (producerReturnPending value) = .error .sourceIncomplete := ⟨rfl,rfl⟩

theorem reclaim_after_source_acquire_is_rejected (value : Nat) :
    Ordered.Client.step code launch (.protocol (.reclaim 0)) (afterAcquire value) = .error (.protocolFailure .outstandingLoan) := by
  apply Ordered.Client.source_step_cannot_discharge_loan (actual_acquire_step value) (buffer := {value := value,loans := [⟨⟨0,1⟩,.read⟩]})
  · rfl
  · rfl

theorem source_exit_alone_does_not_return_loans (value : Nat) :
    Ordered.Client.step code launch (.protocol (.reclaim 0)) (Client.sourceFinal value) = .error (.protocolFailure .outstandingLoan) := rfl

theorem device_completion_alone_does_not_return_loans (value : Nat) :
    Ordered.Client.run code launch [.protocol (.device 0),.protocol (.reclaim 0)] (Client.sourceFinal value) =
      .error (.protocolFailure .outstandingLoan) := rfl

theorem host_acquire_before_device_is_rejected (value : Nat) :
    Ordered.Client.step code launch (.protocol (.acquire 9)) (Client.sourceFinal value) = .error (.protocolFailure .notComplete) := rfl

theorem incomplete_source_is_not_success_adequate (value : Nat) :
    ¬adequate .NotStuck (IrisOrderedClient.invoke code launch (.protocol (.device 0))) (afterAcquire value)
      (fun result _ => ∃ next, result = .ok next) :=
  IrisOrderedClient.reject_not_ok_adequate (device_cannot_complete_at_acquire value)

theorem missing_host_acquire_is_not_success_adequate (value : Nat) :
    ¬adequate .NotStuck
      (IrisOrderedClient.script code launch [.protocol (.device 0),.protocol (.reclaim 0)]) (Client.sourceFinal value)
      (fun result _ => ∃ next, result = .ok next) :=
  IrisOrderedClient.script_reject_not_ok_adequate (device_completion_alone_does_not_return_loans value)

theorem actual_source_and_protocol_have_closed_adequacy (value : Nat) :
    adequate .NotStuck (IrisOrderedClient.script code launch Client.actions) (Client.initial value)
      (fun result _ => result = .ok (Client.final value) ∧ Post launch.initial (Client.observation launch.initial).output ∧
        Ordered.WellFormed code launch (Client.final value).source ∧ Async.Invariant (Client.final value).protocol) :=
  Client.native_client_adequate value launch ⟨⟨rfl,rfl⟩,OrderedLoopTests.zero_initial_flag_is_represented⟩

end
end Ptx.OrderedClientTests
