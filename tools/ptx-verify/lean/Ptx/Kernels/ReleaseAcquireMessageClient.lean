import Ptx.Kernels.ReleaseAcquireMessageUniversal
import Ptx.Iris.OrderedClient
import Ptx.Async.Contracts

/-! An actual source/protocol/Iris client for the fixed message translation.
The protocol reservation is an opaque lifetime obligation. Its scalar value is
arbitrary and is not identified with DATA/FLAG/OUT. The joint completion guard
does not replace byte/region reservation coverage or physical runtime refinement.
-/
namespace Ptx.Kernels.ReleaseAcquireMessage.Client
open Ptx.ISA
open Iris Iris.ProgramLogic
noncomputable section

def initial (value : Nat) : Ordered.Client.State :=
  ⟨Ordered.Client.reset candidate,Async.Contracts.deferredIssued value⟩
def sourceActions : List Ordered.Client.Action :=
  List.replicate 9 (.source 0) ++ List.replicate 12 (.source 1)
def sourceFinal (value : Nat) : Ordered.Client.State := ⟨candidate,Async.Contracts.deferredIssued value⟩
def actions : List Ordered.Client.Action := sourceActions ++ [.protocol (.device 0),.protocol (.acquire 9),.protocol (.reclaim 0)]
def final (value : Nat) : Ordered.Client.State := ⟨candidate,Async.Contracts.deferredFinal value⟩
def observation (initial : Scalar.ByteMap) : Scalar.Observation :=
  Ptx.Event.selectedObservation candidate.view initial (Ptx.Event.writerSelector candidate.view) domain

theorem initial_well_formed (value : Nat) : Ordered.WellFormed code launch (initial value).source :=
  Ordered.Client.reset_well_formed source_candidate_is_well_formed

theorem initial_protocol_invariant (value : Nat) : Async.Invariant (initial value).protocol :=
  Async.steps_invariant (Async.initial_invariant _ _) (Async.run_sound (Async.Contracts.deferred_issued value))

theorem actual_source_run (value : Nat) :
    Ordered.Client.run code launch sourceActions (initial value) = .ok (sourceFinal value) := by
  let mid : Ordered.Client.State := ⟨⟨[trace 0 9,Ordered.Client.resetTrace (trace 1 12)]⟩,Async.Contracts.deferredIssued value⟩
  have h0 : Ordered.Client.run code launch (List.replicate 9 (.source 0)) (initial value) = .ok mid := by
    rw [Ordered.Client.source_actions_run (code := code) (launch := launch) (state := initial value) (index := 0) (count := 9)
      (trace := Ordered.Client.resetTrace (trace 0 9)) rfl producer_source_run]
    rfl
  have h1 : Ordered.Client.run code launch (List.replicate 12 (.source 1)) mid = .ok (sourceFinal value) := by
    rw [Ordered.Client.source_actions_run (code := code) (launch := launch) (state := mid) (index := 1) (count := 12)
      (trace := Ordered.Client.resetTrace (trace 1 12)) rfl consumer_source_run]
    rfl
  rw [sourceActions,Ordered.Client.run_append,h0]
  exact h1

theorem actual_full_client_run (value : Nat) :
    Ordered.Client.run code launch actions (initial value) = .ok (final value) := by
  rw [actions,Ordered.Client.run_append,actual_source_run]
  rfl

theorem final_source_complete (value : Nat) : Ordered.Complete (final value).source := source_candidate_is_complete

theorem loans_returned_and_reclaimed (value : Nat) :
    (final value).protocol.buffers[0]? = some {value := value,alive := false,loans := []} := rfl

theorem native_client_adequate (value : Nat) (actualLaunch : Scalar.Launch) (hp : Pre actualLaunch) :
    adequate .NotStuck (IrisOrderedClient.script code actualLaunch actions) (initial value)
      (fun result _ => result = .ok (final value) ∧ Post actualLaunch.initial (observation actualLaunch.initial).output ∧
        Ordered.WellFormed code actualLaunch (final value).source ∧ Async.Invariant (final value).protocol) := by
  have hw : Ordered.WellFormed code actualLaunch (initial value).source :=
    Ordered.Client.reset_well_formed (source_well_formed_for_initial hp.1)
  have hr : Ordered.Client.run code actualLaunch actions (initial value) = .ok (final value) := by
    rw [Ordered.Client.run_launch_eq hp.1.1 hp.1.2]
    exact actual_full_client_run value
  apply IrisOrderedClient.contract_adequate correct hp hw (initial_protocol_invariant value)
    hr (final_source_complete value) (actual_memory_consistent actualLaunch.initial)
  · exact Ordered.unique_writers_observation source_candidate_is_complete domain_global
      (fun _ _ _ _ _ ha hb => unique_byte_writer ha hb)
  · rfl

end
end Ptx.Kernels.ReleaseAcquireMessage.Client
