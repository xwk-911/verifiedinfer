import Ptx.Iris.ByteContentsPreparation

/-! Construct native public preparation from real ready-request rules, seal
the exact queue and embed the subsequent checked source/protocol execution.
The reserved event cannot be overwritten by ordinary protocol commands.
-/
namespace Ptx.ByteContentsPreparation
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
open Ptx.ByteContentsHeap
noncomputable section

theorem coupled_step_preserves_event {block candidate histories cluster plan before after event ticket}
    (hs : Bridge.Step block Tma.localShared candidate histories cluster plan before after)
    (he : Ptx.Async.getEvent before.protocol event = .ok ticket) : Ptx.Async.getEvent after.protocol event = .ok ticket := by
  cases hs with
  | access advance => exact he
  | host action run => exact Ptx.Async.host_preserves_recorded_event action run he
  | device stream run completion => simpa only [Ptx.Async.getEvent,Ptx.Async.deviceStep_preserves_events run] using he

theorem execute_preserves_enabled {ctx action state next} (he : Enabled ctx state)
    (hs : ByteContentsProtocolHeap.transition ctx.execution action state = .ok next) : Enabled ctx next := by
  cases action with
  | source action =>
    have hp := ByteContentsHeap.action_protocol ctx.execution.source hs
    simpa only [Enabled,hp] using he
  | protocol command =>
    exact coupled_step_preserves_event (ByteContents.executeCommand_spec (block := ctx.execution.source.block) hs).2.1 he

theorem execution_run (ctx : Context) (actions : List ByteContentsProtocolHeap.Action) {state next}
    (he : Enabled ctx state) (hr : IrisExecution.run (ByteContentsProtocolHeap.transition ctx.execution) actions state = .ok next) :
    IrisExecution.run (transition ctx) (execution actions) state = .ok next ∧ Enabled ctx next := by
  induction actions generalizing state with
  | nil => cases hr; exact ⟨rfl,he⟩
  | cons head rest ih =>
    change (ByteContentsProtocolHeap.transition ctx.execution head state).bind _ = .ok next at hr
    cases hs : ByteContentsProtocolHeap.transition ctx.execution head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid =>
      obtain ⟨hrun,hfinal⟩ := ih (execute_preserves_enabled he hs) (by simpa only [hs,Except.bind] using hr)
      refine ⟨?_,hfinal⟩
      change (transition ctx (.execute head) state).bind _ = .ok next
      rw [execution_step he,hs]
      exact hrun

theorem execution_projects (ctx : Context) (actions : List ByteContentsProtocolHeap.Action) {state next}
    (hr : IrisExecution.run (transition ctx) (execution actions) state = .ok next) :
    IrisExecution.run (ByteContentsProtocolHeap.transition ctx.execution) actions state = .ok next := by
  induction actions generalizing state with
  | nil => cases hr; rfl
  | cons head rest ih =>
    change (transition ctx (.execute head) state).bind _ = .ok next at hr
    cases hs : transition ctx (.execute head) state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid =>
      have ht := ih (by simpa only [hs,Except.bind,execution] using hr)
      change (ByteContentsProtocolHeap.transition ctx.execution head state).bind _ = .ok next
      rw [(execute_spec hs).2]
      exact ht

theorem request_ready_step {ctx state before} (request : Ptx.Async.Preparation.Request)
    (hp : CanPrepare ctx state) (hr : Ptx.Async.Preparation.Ready state.coupled.protocol before)
    (hv : request.Valid state.coupled.protocol.buffers.length) :
    ∃ next, transition ctx (.request request) state = .ok next ∧
      Ptx.Async.Preparation.Ready next.coupled.protocol (before++[request.command]) ∧ CanPrepare ctx next ∧
      next.cells = state.cells ∧ next.coupled.done = state.coupled.done ∧ next.coupled.protocol.events = state.coupled.protocol.events := by
  have hh : ∃ protocol, Ptx.Async.step state.coupled.protocol request.action = .ok protocol ∧
      Ptx.Async.Preparation.Ready protocol (before++[request.command]) ∧ protocol.events = state.coupled.protocol.events := by
    cases request with
    | use bid => exact Ptx.Async.Preparation.ready_use hr hv
    | access bid mode => exact Ptx.Async.Preparation.ready_access mode hr hv
    | copy src dst => exact Ptx.Async.Preparation.ready_copy hr hv.1 hv.2.1 hv.2.2
  obtain ⟨protocol,hs,hready,he⟩ := hh
  refine ⟨ByteContents.withCoupled state ⟨protocol,state.coupled.done⟩,request_success hp hs,hready,?_,rfl,rfl,he⟩
  refine ⟨hp.1,?_⟩
  change protocol.events.any (fun entry => entry.id == ctx.event) = false
  rw [he]
  exact hp.2

theorem requests_run (ctx : Context) (items : List Ptx.Async.Preparation.Request) {state before}
    (hp : CanPrepare ctx state) (hr : Ptx.Async.Preparation.Ready state.coupled.protocol before)
    (hv : ∀ request ∈ items, request.Valid state.coupled.protocol.buffers.length) :
    ∃ next, IrisExecution.run (transition ctx) (requests items) state = .ok next ∧
      Ptx.Async.Preparation.Ready next.coupled.protocol (before++items.map Ptx.Async.Preparation.Request.command) ∧
      CanPrepare ctx next ∧ next.cells = state.cells ∧ next.coupled.done = state.coupled.done ∧
      next.coupled.protocol.events = state.coupled.protocol.events := by
  induction items generalizing state before with
  | nil => exact ⟨state,rfl,by simpa using hr,hp,rfl,rfl,rfl⟩
  | cons head rest ih =>
    obtain ⟨mid,hs,hready,hprepare,hcells,hcut,hevents⟩ := request_ready_step head hp hr (hv head (by simp))
    have hlen := Ptx.Async.step_buffers_length (publicStep_spec (request_spec hs).2).1
    obtain ⟨next,ht,hready',hprepare',hcells',hcut',hevents'⟩ := ih hprepare hready (by
      intro request hm
      rw [hlen]
      exact hv request (by simp [hm]))
    refine ⟨next,?_,?_,hprepare',hcells'.trans hcells,hcut'.trans hcut,hevents'.trans hevents⟩
    · change (transition ctx (.request head) state).bind _ = .ok next
      rw [hs]
      exact ht
    · simpa only [List.map_cons,List.append_assoc,List.singleton_append] using hready'

theorem requests_public_run (ctx : Context) (items : List Ptx.Async.Preparation.Request) {state next}
    (hr : IrisExecution.run (transition ctx) (requests items) state = .ok next) :
    Ptx.Async.run state.coupled.protocol (items.map Ptx.Async.Preparation.Request.action) = .ok next.coupled.protocol := by
  induction items generalizing state with
  | nil => cases hr; rfl
  | cons head rest ih =>
    change (transition ctx (.request head) state).bind _ = .ok next at hr
    cases hs : transition ctx (.request head) state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid =>
      have ht := ih (by simpa only [hs,Except.bind,requests] using hr)
      have hh := (publicStep_spec (request_spec hs).2).1
      simp only [List.map_cons,Ptx.Async.run,hh,Except.bind]
      exact ht

theorem seal_ready_state (ctx : Context) (state : State) (hp : CanPrepare ctx state)
    (hr : Ptx.Async.Preparation.Ready state.coupled.protocol ctx.commands) :
    ∃ next, transition ctx .seal state = .ok next ∧ Enabled ctx next ∧
      next.cells = state.cells ∧ next.coupled.done = state.coupled.done := by
  let protocol : Ptx.Async.State := {state.coupled.protocol with events := ⟨ctx.event,⟨0,ctx.commands.length⟩⟩::state.coupled.protocol.events}
  have hs : Ptx.Async.step state.coupled.protocol (.record 0 ctx.event) = .ok protocol :=
    Ptx.Async.Preparation.ready_record hr hp.2
  refine ⟨ByteContents.withCoupled state ⟨protocol,state.coupled.done⟩,seal_success hp hr hs,?_,rfl,rfl⟩
  simp [Enabled,protocol,ByteContents.withCoupled,Ptx.Async.getEvent,bind,Except.bind,Pure.pure,Except.pure]

theorem prepare_run (ctx : Context) (items : List Ptx.Async.Preparation.Request) (state : State)
    (hp : CanPrepare ctx state) (hr : Ptx.Async.Preparation.Ready state.coupled.protocol [])
    (hv : ∀ request ∈ items, request.Valid state.coupled.protocol.buffers.length)
    (hc : items.map Ptx.Async.Preparation.Request.command = ctx.commands) :
    ∃ next, IrisExecution.run (transition ctx) (requests items ++ [.seal]) state = .ok next ∧ Enabled ctx next ∧
      next.cells = state.cells ∧ next.coupled.done = state.coupled.done ∧
      Ptx.Async.run state.coupled.protocol (items.map Ptx.Async.Preparation.Request.action ++ [.record 0 ctx.event]) = .ok next.coupled.protocol := by
  obtain ⟨mid,hs,hready,hprepare,hcells,hcut,_⟩ := requests_run ctx items hp hr hv
  have hready' : Ptx.Async.Preparation.Ready mid.coupled.protocol ctx.commands := by simpa only [List.nil_append,hc] using hready
  obtain ⟨next,ht,hen,hcells',hcut'⟩ := seal_ready_state ctx mid hprepare hready'
  refine ⟨next,?_,hen,hcells'.trans hcells,hcut'.trans hcut,?_⟩
  · rw [IrisExecution.run_append,hs]
    change IrisExecution.run (transition ctx) [.seal] mid = .ok next
    rw [IrisExecution.run_singleton]
    exact ht
  · rw [Ptx.Async.Client.run_append,requests_public_run ctx items hs]
    change (Ptx.Async.step mid.coupled.protocol (.record 0 ctx.event)).bind _ = .ok next.coupled.protocol
    rw [(publicStep_spec (seal_spec ht).2.2).1]
    rfl

theorem enabled_not_preparable {ctx state} (he : Enabled ctx state) : ¬CanPrepare ctx state := by
  intro hp
  have hi := Ptx.Async.event_fresh_invalid hp.2
  change Ptx.Async.getEvent state.coupled.protocol ctx.event = .ok _ at he
  rw [hi] at he
  cases he

theorem request_after_seal_rejected {ctx state request} (he : Enabled ctx state) :
    transition ctx (.request request) state = .error .preparationClosed := request_closed (enabled_not_preparable he)

theorem seal_after_seal_rejected {ctx state} (he : Enabled ctx state) :
    transition ctx .seal state = .error .preparationClosed := by
  simp only [transition,enabled_not_preparable he,ite_false]

theorem unique_writes_action (ctx : Context) {action state next}
    (hi : ByteContentsHeap.UniqueWrites ctx.execution.source state) (hs : transition ctx action state = .ok next) :
    ByteContentsHeap.UniqueWrites ctx.execution.source next := by
  have hp : ∀ protocolAction, publicStep protocolAction state = .ok next → ByteContentsHeap.UniqueWrites ctx.execution.source next := by
    intro protocolAction hr writer loc value hw hu hd
    have hh := publicStep_spec hr
    rw [hh.2.1] at hd
    change (get? next.cells (ByteAuthority.key loc)).bind ByteContents.Payload.value = some value
    rw [hh.2.2]
    exact hi writer loc value hw hu hd
  cases action with
  | request request => exact hp _ (request_spec hs).2
  | «seal» => exact hp _ (seal_spec hs).2.2
  | execute action => exact ByteContentsProtocolHeap.unique_writes_action ctx.execution hi (execute_spec hs).2

theorem unique_writes_run (ctx : Context) (actions : List Action) {state next}
    (hi : ByteContentsHeap.UniqueWrites ctx.execution.source state) (hr : IrisExecution.run (transition ctx) actions state = .ok next) :
    ByteContentsHeap.UniqueWrites ctx.execution.source next := by
  induction actions generalizing state with
  | nil => cases hr; exact hi
  | cons head rest ih =>
    change (transition ctx head state).bind _ = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid => exact ih (unique_writes_action ctx hi hs) (by simpa only [hs,Except.bind] using hr)

def IsPreparation : Action → Prop
  | .request _ | .seal => True
  | .execute _ => False

theorem preparation_preserves_cells {ctx action state next} (hp : IsPreparation action)
    (hs : transition ctx action state = .ok next) : next.cells = state.cells := by
  cases action with
  | request request => exact (publicStep_spec (request_spec hs).2).2.2
  | «seal» => exact (publicStep_spec (seal_spec hs).2.2).2.2
  | execute action => cases hp

theorem preparation_local_cps [GS] (ctx : Context) (action : Action) (state next : State) (tail : List Action)
    (frame : IProp GF) (post : Except ByteContents.Error State → IProp GF) (hp : IsPreparation action)
    (hs : transition ctx action state = .ok next)
    (hcont : control next ∗ frame ⊢ WP (script ctx tail) {{ result, post result }}) :
    control state ∗ frame ⊢ WP (script ctx (action::tail)) {{ result, post result }} := by
  apply ByteContentsMachine.step_script_wp (transition ctx) state next action tail frame frame post hs ?_ hcont
  iintro ⟨Hheap,Hcontrol,Hframe⟩
  imod ByteContentsProtocolHeap.protocol_update_local state next (preparation_preserves_cells hp hs) $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
  imodintro
  iframe Hheap Hcontrol Hframe

theorem preparation_local_wp [GS] (ctx : Context) (action : Action) (state next : State) (frame : IProp GF)
    (hp : IsPreparation action) (hs : transition ctx action state = .ok next) :
    control state ∗ frame ⊢ WP (script ctx [action]) {{ result, ⌜result = .ok next⌝ ∗ control next ∗ frame }} := by
  apply preparation_local_cps ctx action state next [] frame _ hp hs
  exact ByteContentsMachine.script_nil_wp (transition ctx) next frame

end
end Ptx.ByteContentsPreparation
