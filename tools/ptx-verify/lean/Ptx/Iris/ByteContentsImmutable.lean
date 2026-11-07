import Ptx.Iris.ByteContentsPreparationExecution

/-! Unwritten modeled byte values survive every checked client action.
Preparation and protocol commands only change metadata. Source actions retain
their original emitted-write semantics. This is not a statement about physical
host-write/reclaim effects, which this protocol language does not simulate.
-/
namespace Ptx.ByteContentsPreparation
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

theorem immutable_value_action (ctx : Context) {action state next} (loc : Location)
    (hw : ∀ node, ByteContents.writeByte ctx.execution.source.candidate node loc = none)
    (hs : transition ctx action state = .ok next) : ByteContents.valueAt next loc = ByteContents.valueAt state loc := by
  have hp : ∀ command, publicStep command state = .ok next → ByteContents.valueAt next loc = ByteContents.valueAt state loc := by
    intro command hr
    unfold ByteContents.valueAt
    rw [(publicStep_spec hr).2.2]
  cases action with
  | request request => exact hp _ (request_spec hs).2
  | «seal» => exact hp _ (seal_spec hs).2.2
  | execute action =>
    have hh := (execute_spec hs).2
    cases action with
    | protocol command => exact ByteContents.executeCommand_value hh loc
    | source action =>
      cases action with
      | claim request => exact ByteContents.claim_preserves_value hh loc
      | control node => exact ByteContents.finishControl_preserves_value hh loc
      | finish memory demands => exact ByteContents.finish_preserves_unwritten hh (hw memory)

theorem immutable_value_run (ctx : Context) (actions : List Action) {state next} (loc : Location)
    (hw : ∀ node, ByteContents.writeByte ctx.execution.source.candidate node loc = none)
    (hr : IrisExecution.run (transition ctx) actions state = .ok next) : ByteContents.valueAt next loc = ByteContents.valueAt state loc := by
  induction actions generalizing state with
  | nil => cases hr; rfl
  | cons head rest ih =>
    change (transition ctx head state).bind _ = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid => exact (ih (by simpa only [hs,Except.bind] using hr)).trans (immutable_value_action ctx loc hw hs)

end
end Ptx.ByteContentsPreparation
