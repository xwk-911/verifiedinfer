import Ptx.Iris.ByteContentsProtocol
import Ptx.Async.RecordedEvents
import Ptx.Async.Preparation

/-! Public preparation and execution in the same symbolic-byte state.
Preparation requires an untouched source cut, an available byte pool and a
fresh reserved event. Sealing checks the exact prepared queue before recording
its frontier. Execution requires that recorded frontier. Preparation cannot
extend a sealed plan or run while source byte claims are active. These are
modeled protocol operations, not physical allocation or CUDA runtime calls.
-/
namespace Ptx.ByteContentsPreparation
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
open Ptx.ByteContentsHeap
noncomputable section

abbrev State := ByteContents.State
structure Context where
  execution : ByteContentsProtocolHeap.Context
  commands : List Ptx.Async.Command
  event : Nat
inductive Action
  | request (request : Ptx.Async.Preparation.Request)
  | seal
  | execute (action : ByteContentsProtocolHeap.Action)

def Quiet (state : State) : Prop := (∀ node, ¬state.coupled.done node) ∧ Available state
def CanPrepare (ctx : Context) (state : State) : Prop :=
  Quiet state ∧ state.coupled.protocol.events.any (fun entry => entry.id == ctx.event) = false
def Enabled (ctx : Context) (state : State) : Prop :=
  Ptx.Async.getEvent state.coupled.protocol ctx.event = .ok ⟨0,ctx.commands.length⟩

def publicStep (action : Ptx.Async.Action) (state : State) : Except ByteContents.Error State :=
  match Ptx.Async.step state.coupled.protocol action with
  | .error error => .error (.authority (.protocolFailure error))
  | .ok protocol => .ok (ByteContents.withCoupled state ⟨protocol,state.coupled.done⟩)

noncomputable def transition (ctx : Context) (action : Action) (state : State) : Except ByteContents.Error State := by
  classical
  exact match action with
  | .request request => if CanPrepare ctx state then publicStep request.action state else .error .preparationClosed
  | .seal => if CanPrepare ctx state then
      if Ptx.Async.Preparation.Ready state.coupled.protocol ctx.commands then publicStep (.record 0 ctx.event) state
      else .error .preparationNotReady
    else .error .preparationClosed
  | .execute action => if Enabled ctx state then ByteContentsProtocolHeap.transition ctx.execution action state else .error .unprepared

abbrev script (ctx : Context) (actions : List Action) := ByteContentsMachine.script (transition ctx) actions
def requests (items : List Ptx.Async.Preparation.Request) := items.map Action.request
def execution (actions : List ByteContentsProtocolHeap.Action) := actions.map Action.execute

theorem publicStep_success {action state protocol} (hs : Ptx.Async.step state.coupled.protocol action = .ok protocol) :
    publicStep action state = .ok (ByteContents.withCoupled state ⟨protocol,state.coupled.done⟩) := by simp only [publicStep,hs]

theorem publicStep_error {action state error} (hs : Ptx.Async.step state.coupled.protocol action = .error error) :
    publicStep action state = .error (.authority (.protocolFailure error)) := by simp only [publicStep,hs]

theorem publicStep_spec {action state next} (hs : publicStep action state = .ok next) :
    Ptx.Async.step state.coupled.protocol action = .ok next.coupled.protocol ∧
      next.coupled.done = state.coupled.done ∧ next.cells = state.cells := by
  unfold publicStep at hs
  cases hr : Ptx.Async.step state.coupled.protocol action with
  | error error => simp [hr] at hs
  | ok protocol =>
    have hn : next = ByteContents.withCoupled state ⟨protocol,state.coupled.done⟩ := (Except.ok.inj (by simpa only [hr] using hs)).symm
    subst next
    exact ⟨rfl,rfl,rfl⟩

theorem request_success {ctx request state protocol} (hp : CanPrepare ctx state)
    (hs : Ptx.Async.step state.coupled.protocol request.action = .ok protocol) :
    transition ctx (.request request) state = .ok (ByteContents.withCoupled state ⟨protocol,state.coupled.done⟩) := by
  simp only [transition,hp,ite_true]
  exact publicStep_success hs

theorem seal_success {ctx state protocol} (hp : CanPrepare ctx state)
    (hr : Ptx.Async.Preparation.Ready state.coupled.protocol ctx.commands)
    (hs : Ptx.Async.step state.coupled.protocol (.record 0 ctx.event) = .ok protocol) :
    transition ctx .seal state = .ok (ByteContents.withCoupled state ⟨protocol,state.coupled.done⟩) := by
  simp only [transition,hp,hr,ite_true]
  exact publicStep_success hs

theorem request_closed {ctx request state} (hp : ¬CanPrepare ctx state) :
    transition ctx (.request request) state = .error .preparationClosed := by simp only [transition,hp,ite_false]

theorem seal_incomplete {ctx state} (hp : CanPrepare ctx state)
    (hr : ¬Ptx.Async.Preparation.Ready state.coupled.protocol ctx.commands) :
    transition ctx .seal state = .error .preparationNotReady := by simp only [transition,hp,hr,ite_true,ite_false]

theorem execution_unprepared {ctx action state} (he : ¬Enabled ctx state) :
    transition ctx (.execute action) state = .error .unprepared := by simp only [transition,he,ite_false]

theorem execution_step {ctx action state} (he : Enabled ctx state) :
    transition ctx (.execute action) state = ByteContentsProtocolHeap.transition ctx.execution action state := by simp only [transition,he,ite_true]

theorem request_spec {ctx request state next} (hs : transition ctx (.request request) state = .ok next) :
    CanPrepare ctx state ∧ publicStep request.action state = .ok next := by
  classical
  change (if CanPrepare ctx state then publicStep request.action state else .error .preparationClosed) = .ok next at hs
  split at hs
  · exact ⟨‹CanPrepare ctx state›,hs⟩
  · cases hs

theorem seal_spec {ctx state next} (hs : transition ctx .seal state = .ok next) :
    CanPrepare ctx state ∧ Ptx.Async.Preparation.Ready state.coupled.protocol ctx.commands ∧ publicStep (.record 0 ctx.event) state = .ok next := by
  classical
  change (if CanPrepare ctx state then
    if Ptx.Async.Preparation.Ready state.coupled.protocol ctx.commands then publicStep (.record 0 ctx.event) state else .error .preparationNotReady
    else .error .preparationClosed) = .ok next at hs
  split at hs
  · split at hs
    · exact ⟨‹CanPrepare ctx state›,‹Ptx.Async.Preparation.Ready state.coupled.protocol ctx.commands›,hs⟩
    · cases hs
  · cases hs

theorem execute_spec {ctx action state next} (hs : transition ctx (.execute action) state = .ok next) :
    Enabled ctx state ∧ ByteContentsProtocolHeap.transition ctx.execution action state = .ok next := by
  classical
  change (if Enabled ctx state then ByteContentsProtocolHeap.transition ctx.execution action state else .error .unprepared) = .ok next at hs
  split at hs
  · exact ⟨‹Enabled ctx state›,hs⟩
  · cases hs

theorem action_domain (ctx : Context) {action state next} (hs : transition ctx action state = .ok next) : dom state.cells = dom next.cells := by
  cases action with
  | request request => rw [(publicStep_spec (request_spec hs).2).2.2]
  | «seal» => rw [(publicStep_spec (seal_spec hs).2.2).2.2]
  | execute action => exact ByteContentsProtocolHeap.action_domain ctx.execution (execute_spec hs).2

theorem script_wp [GS] (ctx : Context) (actions : List Action) (state final : State) (frame : IProp GF)
    (hr : IrisExecution.run (transition ctx) actions state = .ok final) :
    allPoints state ∗ frame ⊢ WP (script ctx actions) {{ result, ⌜result = .ok final⌝ ∗ allPoints final ∗ frame }} :=
  ByteContentsMachine.script_wp (transition ctx) actions state final frame (fun _ _ _ h => action_domain ctx h) hr

theorem script_adequate (ctx : Context) (actions : List Action) (state final : State)
    (hr : IrisExecution.run (transition ctx) actions state = .ok final) :
    adequate .NotStuck (script ctx actions) state (fun result _ => result = .ok final) :=
  ByteContentsMachine.script_adequate (transition ctx) actions state final (fun _ _ _ h => action_domain ctx h) hr

end
end Ptx.ByteContentsPreparation
