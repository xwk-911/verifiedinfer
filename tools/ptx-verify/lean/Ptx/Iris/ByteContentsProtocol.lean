import Ptx.Hopper.ByteContentsProtocol
import Ptx.Iris.ByteContentsMachine
import Ptx.Iris.ByteContentsWrites

/-! One value-state language for actual source actions and checked prepared-plan
commands. Source actions retain their existing interpreter. Protocol commands
retain source-matched completion and original errors and leave byte cells alone.
Closed adequacy uses the existing whole-map native heap baseline. Controller-only
protocol rules frame all byte fragments, including fractional fragments.
-/
namespace Ptx.ByteContentsProtocolHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
open Ptx.ByteContentsHeap
noncomputable section

abbrev State := ByteContents.State
structure Context where
  source : ByteContentsHeap.Context
  cluster : Access.ClusterScope
  plan : Bridge.Plan
inductive Action
  | source (action : ByteContentsHeap.Action)
  | protocol (command : Bridge.Command)
def transition (ctx : Context) : Action → State → Except ByteContents.Error State
  | .source action => ByteContentsHeap.transition ctx.source action
  | .protocol command => ByteContents.executeCommand ctx.source.candidate ctx.source.histories ctx.cluster ctx.plan command
abbrev script (ctx : Context) (actions : List Action) := ByteContentsMachine.script (transition ctx) actions
def sourceActions (actions : List ByteContentsHeap.Action) := actions.map Action.source
def protocolActions (commands : List Bridge.Command) := commands.map Action.protocol

theorem protocol_error (ctx : Context) {command state error}
    (hs : ByteAuthority.executeCommand ctx.source.candidate ctx.source.histories ctx.cluster ctx.plan command (ByteContents.erase state) = .error error) :
    transition ctx (.protocol command) state = .error (.authority error) := ByteContents.executeCommand_error hs

theorem source_run (ctx : Context) (actions : List ByteContentsHeap.Action) (state : State) :
    IrisExecution.run (transition ctx) (sourceActions actions) state = IrisExecution.run (ByteContentsHeap.transition ctx.source) actions state := by
  induction actions generalizing state with
  | nil => rfl
  | cons head rest ih =>
    change (ByteContentsHeap.transition ctx.source head state).bind _ = (ByteContentsHeap.transition ctx.source head state).bind _
    cases hs : ByteContentsHeap.transition ctx.source head state with
    | error error => rfl
    | ok mid => exact ih mid

theorem protocol_run (ctx : Context) (commands : List Bridge.Command) (state : State) :
    IrisExecution.run (transition ctx) (protocolActions commands) state =
      ByteContents.runCommands ctx.source.candidate ctx.source.histories ctx.cluster ctx.plan commands state := by
  induction commands generalizing state with
  | nil => rfl
  | cons head rest ih =>
    change (ByteContents.executeCommand ctx.source.candidate ctx.source.histories ctx.cluster ctx.plan head state).bind _ =
      (ByteContents.executeCommand ctx.source.candidate ctx.source.histories ctx.cluster ctx.plan head state).bind _
    cases hs : ByteContents.executeCommand ctx.source.candidate ctx.source.histories ctx.cluster ctx.plan head state with
    | error error => rfl
    | ok mid => exact ih mid

theorem action_domain (ctx : Context) {action state next} (hs : transition ctx action state = .ok next) :
    dom state.cells = dom next.cells := by
  cases action with
  | source action => exact ByteContentsHeap.action_domain ctx.source hs
  | protocol command => rw [(ByteContents.executeCommand_spec (block := ctx.source.block) hs).2.2.2]

theorem action_projects (ctx : Context) {action state next} (hs : transition ctx action state = .ok next) :
    ByteAuthority.Step ctx.source.block ctx.source.candidate ctx.source.histories ctx.cluster ctx.plan (ByteContents.erase state) (ByteContents.erase next) := by
  cases action with
  | source action => exact ByteContentsHeap.action_projects ctx.source hs
  | protocol command => exact ByteContents.executeCommand_projects hs

theorem run_projects (ctx : Context) (actions : List Action) {state next}
    (hr : IrisExecution.run (transition ctx) actions state = .ok next) :
    ByteAuthority.Steps ctx.source.block ctx.source.candidate ctx.source.histories ctx.cluster ctx.plan (ByteContents.erase state) (ByteContents.erase next) := by
  induction actions generalizing state with
  | nil => cases hr; exact .refl _
  | cons head rest ih =>
    change (transition ctx head state).bind _ = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid => exact .next (action_projects ctx hs) (ih (by simpa only [hs,Except.bind] using hr))

theorem unique_writes_action (ctx : Context) {action state next}
    (hi : ByteContentsHeap.UniqueWrites ctx.source state) (hs : transition ctx action state = .ok next) :
    ByteContentsHeap.UniqueWrites ctx.source next := by
  cases action with
  | source action => exact ByteContentsHeap.unique_writes_action hi hs
  | protocol command =>
    intro writer loc value hw hu hd
    rw [(ByteContents.executeCommand_spec (block := ctx.source.block) hs).2.2.1] at hd
    rw [ByteContents.executeCommand_value hs loc]
    exact hi writer loc value hw hu hd

theorem unique_writes_run (ctx : Context) (actions : List Action) {state next}
    (hi : ByteContentsHeap.UniqueWrites ctx.source state) (hr : IrisExecution.run (transition ctx) actions state = .ok next) :
    ByteContentsHeap.UniqueWrites ctx.source next := by
  induction actions generalizing state with
  | nil => cases hr; exact hi
  | cons head rest ih =>
    change (transition ctx head state).bind _ = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid => exact ih (unique_writes_action ctx hi hs) (by simpa only [hs,Except.bind] using hr)

theorem protocol_preserves_cells_and_cut (ctx : Context) (commands : List Bridge.Command) {state next}
    (hr : IrisExecution.run (transition ctx) (protocolActions commands) state = .ok next) :
    next.cells = state.cells ∧ next.coupled.done = state.coupled.done := by
  induction commands generalizing state with
  | nil => cases hr; exact ⟨rfl,rfl⟩
  | cons head rest ih =>
    change (ByteContents.executeCommand ctx.source.candidate ctx.source.histories ctx.cluster ctx.plan head state).bind _ = .ok next at hr
    cases hs : ByteContents.executeCommand ctx.source.candidate ctx.source.histories ctx.cluster ctx.plan head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid =>
      obtain ⟨hc,hd⟩ := ih (by simpa only [hs,Except.bind,protocolActions] using hr)
      have hh := ByteContents.executeCommand_spec (block := ctx.source.block) hs
      exact ⟨hc.trans hh.2.2.2,hd.trans hh.2.2.1⟩

theorem completed_protocol_run (ctx : Context) (commands : List Bridge.Command) (state : State) (final : Ptx.Async.State)
    (hc : Bridge.AllCompleted Tma.localShared ctx.source.candidate ctx.source.histories ctx.cluster ctx.plan state.coupled.done)
    (hr : Ptx.Async.run state.coupled.protocol (commands.map Bridge.Command.action) = .ok final) :
    IrisExecution.run (transition ctx) (protocolActions commands) state = .ok (ByteContents.withCoupled state ⟨final,state.coupled.done⟩) := by
  rw [protocol_run]
  cases state with
  | mk coupled cells =>
    cases coupled with
    | mk protocol done => exact ByteContents.runCommands_succeeds hc commands hr cells

theorem source_protocol_run (ctx : Context) (actions : List ByteContentsHeap.Action) (commands : List Bridge.Command) {state mid final}
    (hs : IrisExecution.run (ByteContentsHeap.transition ctx.source) actions state = .ok mid)
    (hc : Bridge.AllCompleted Tma.localShared ctx.source.candidate ctx.source.histories ctx.cluster ctx.plan mid.coupled.done)
    (hr : Ptx.Async.run mid.coupled.protocol (commands.map Bridge.Command.action) = .ok final) :
    IrisExecution.run (transition ctx) (sourceActions actions ++ protocolActions commands) state =
      .ok (ByteContents.withCoupled mid ⟨final,mid.coupled.done⟩) := by
  rw [IrisExecution.run_append,source_run,hs]
  exact completed_protocol_run ctx commands mid final hc hr

theorem script_wp [GS] (ctx : Context) (actions : List Action) (state final : State) (frame : IProp GF)
    (hr : IrisExecution.run (transition ctx) actions state = .ok final) :
    allPoints state ∗ frame ⊢ WP (script ctx actions) {{ result, ⌜result = .ok final⌝ ∗ allPoints final ∗ frame }} :=
  ByteContentsMachine.script_wp (transition ctx) actions state final frame (fun _ _ _ h => action_domain ctx h) hr

theorem script_adequate (ctx : Context) (actions : List Action) (state final : State)
    (hr : IrisExecution.run (transition ctx) actions state = .ok final) :
    adequate .NotStuck (script ctx actions) state (fun result _ => result = .ok final) :=
  ByteContentsMachine.script_adequate (transition ctx) actions state final (fun _ _ _ h => action_domain ctx h) hr

theorem store_change_controller (before after : State) (hc : after.cells = before.cells) :
    store after = insert (store before) ByteAuthority.controlKey (.control after) := by
  apply equiv_iff_eq.mp
  intro k
  by_cases he : ByteAuthority.controlKey = k
  · subst k; simp [store,get?_insert]
  · simp only [store,get?_insert_ne he,get?_map,hc]

theorem protocol_update_local [GS] (before after : State) (hc : after.cells = before.cells) :
    genHeapInterp (store before) ∗ control before ==∗ genHeapInterp (store after) ∗ control after := by
  unfold ByteContentsHeap.control
  iintro ⟨Hheap,Hcontrol⟩
  imod genHeap_update (v₂ := Cell.control after) $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
  rw [← store_change_controller before after hc]
  imodintro
  iframe Hheap Hcontrol

theorem protocol_local_cps [GS] (ctx : Context) (command : Bridge.Command) (state next : State) (tail : List Action)
    (frame : IProp GF) (post : Except ByteContents.Error State → IProp GF)
    (hs : transition ctx (.protocol command) state = .ok next)
    (hcont : control next ∗ frame ⊢ WP (script ctx tail) {{ result, post result }}) :
    control state ∗ frame ⊢ WP (script ctx (.protocol command::tail)) {{ result, post result }} := by
  apply ByteContentsMachine.step_script_wp (transition ctx) state next (.protocol command) tail frame frame post hs ?_ hcont
  iintro ⟨Hheap,Hcontrol,Hframe⟩
  imod protocol_update_local state next (ByteContents.executeCommand_spec (block := ctx.source.block) hs).2.2.2 $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
  imodintro
  iframe Hheap Hcontrol Hframe

theorem protocol_local_wp [GS] (ctx : Context) (command : Bridge.Command) (state next : State) (frame : IProp GF)
    (hs : transition ctx (.protocol command) state = .ok next) :
    control state ∗ frame ⊢ WP (script ctx [.protocol command])
      {{ result, ⌜result = .ok next⌝ ∗ control next ∗ frame }} := by
  apply protocol_local_cps ctx command state next [] frame _ hs
  exact ByteContentsMachine.script_nil_wp (transition ctx) next frame

end
end Ptx.ByteContentsProtocolHeap
