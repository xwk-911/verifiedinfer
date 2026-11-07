import Ptx.Iris.ByteSourceExecution

/-! Native GenHeap host/device scripts using the fixed context's real plan.
Each command updates the exclusive controller metadata and frames all byte
authority. Its original protocol errors and source-completion guard remain.
This does not interpret protocol scalar buffers as physical GPU byte values.
-/
namespace Ptx.ByteAuthorityHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def protocolActions (commands : List Bridge.Command) : List Action := commands.map Action.protocol

theorem protocol_run (ctx : Context) (commands : List Bridge.Command) (state : State) :
    IrisExecution.run (transition ctx) (protocolActions commands) state =
      ByteAuthority.runCommands ctx.candidate ctx.histories ctx.cluster ctx.plan commands state := by
  induction commands generalizing state with
  | nil => rfl
  | cons head rest ih =>
    change (ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan head state).bind
      (fun mid => IrisExecution.run (transition ctx) (protocolActions rest) mid) =
      (ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan head state).bind
      (fun mid => ByteAuthority.runCommands ctx.candidate ctx.histories ctx.cluster ctx.plan rest mid)
    cases hs : ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan head state with
    | error error => rfl
    | ok mid => exact ih mid

theorem action_is_step (ctx : Context) {action state next}
    (hs : transition ctx action state = .ok next) :
    ByteAuthority.Step ctx.block ctx.candidate ctx.histories ctx.cluster ctx.plan state next := by
  cases action with
  | claim request => exact .claim hs
  | finish node demands => exact ByteAuthority.Footprint.finish_is_authority_step hs
  | protocol command => exact ByteAuthority.executeCommand_is_step hs

theorem run_is_steps (ctx : Context) (actions : List Action) {state next}
    (hr : IrisExecution.run (transition ctx) actions state = .ok next) :
    ByteAuthority.Steps ctx.block ctx.candidate ctx.histories ctx.cluster ctx.plan state next := by
  induction actions generalizing state with
  | nil => cases hr; exact .refl _
  | cons head rest ih =>
    change (transition ctx head state).bind (fun mid => IrisExecution.run (transition ctx) rest mid) = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid => exact .next (action_is_step ctx hs) (ih (by simpa only [hs,Except.bind] using hr))

theorem run_projects (ctx : Context) (actions : List Action) {state next}
    (hr : IrisExecution.run (transition ctx) actions state = .ok next) :
    Bridge.Steps ctx.block Tma.localShared ctx.candidate ctx.histories ctx.cluster ctx.plan state.coupled next.coupled :=
  ByteAuthority.steps_projects (run_is_steps ctx actions hr)

theorem store_change_controller (before after : State) (hb : before.bytes = after.bytes) :
    store after = insert (store before) ByteAuthority.controlKey (.control after) := by
  apply equiv_iff_eq.mp
  intro k
  by_cases hz : ByteAuthority.controlKey = k
  · subst k; simp [store,get?_insert]
  · simp only [store,get?_insert_ne hz,get?_map,hb]

theorem protocol_update [GS] (before after : State) (hb : before.bytes = after.bytes) :
    genHeapInterp (store before) ∗ control before ==∗ genHeapInterp (store after) ∗ control after := by
  unfold control
  iintro ⟨Hheap,Hcontrol⟩
  imod genHeap_update (v₂ := Cell.control after) $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
  rw [← store_change_controller before after hb]
  imodintro
  iframe Hheap Hcontrol

theorem protocol_step_cps [GS] (ctx : Context) (command : Bridge.Command) (state next : State) (tail : List Action)
    (frame : IProp GF) (post : Except ByteAuthority.Error State → IProp GF)
    (hs : ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan command state = .ok next)
    (hcont : allPoints next ∗ frame ⊢ WP (script ctx tail) {{ value, post value }}) :
    allPoints state ∗ frame ⊢ WP (script ctx (.protocol command::tail)) {{ value, post value }} := by
  have hb := (ByteAuthority.executeCommand_spec (block := ctx.block) hs).2.2
  let rest : IProp GF := iprop([∗map] k ↦ value ∈ delete (store state) ByteAuthority.controlKey, pointsTo k (.own 1) value)
  iintro ⟨Hall,Hframe⟩
  icases allPoints_parts state $$ Hall with ⟨Hcontrol,Hrest⟩
  iapply step_script_wp ctx state next (.protocol command) tail iprop(rest ∗ frame) iprop(rest ∗ frame) post hs ?_ ?_
    $$ [$Hcontrol $Hrest $Hframe]
  · iintro ⟨Hheap,Hcontrol,Hrest,Hframe⟩
    imod protocol_update state next hb.symm $$ [$Hheap $Hcontrol] with ⟨Hheap,Hcontrol⟩
    imodintro
    iframe Hheap Hcontrol Hrest Hframe
  · iintro ⟨Hcontrol,Hrest,Hframe⟩
    have hreframe : rest ⊢ iprop([∗map] k ↦ value ∈ delete (store next) ByteAuthority.controlKey, pointsTo k (.own 1) value) := by
      dsimp [rest]
      rw [store_frame_eq state next hb.symm]
    ihave Hrest := hreframe $$ Hrest
    ihave Hall := (allPoints_parts next).2 $$ [$Hcontrol $Hrest]
    iapply hcont $$ [$Hall $Hframe]

theorem protocol_cps [GS] (ctx : Context) (commands : List Bridge.Command) (state final : State) (tail : List Action)
    (frame : IProp GF) (post : Except ByteAuthority.Error State → IProp GF)
    (hr : ByteAuthority.runCommands ctx.candidate ctx.histories ctx.cluster ctx.plan commands state = .ok final)
    (hcont : allPoints final ∗ frame ⊢ WP (script ctx tail) {{ value, post value }}) :
    allPoints state ∗ frame ⊢ WP (script ctx (protocolActions commands ++ tail)) {{ value, post value }} := by
  induction commands generalizing state with
  | nil => cases hr; exact hcont
  | cons command rest ih =>
    unfold ByteAuthority.runCommands at hr
    cases hs : ByteAuthority.executeCommand ctx.candidate ctx.histories ctx.cluster ctx.plan command state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid =>
      have ht := ih mid (by simpa only [hs,Except.bind] using hr)
      exact protocol_step_cps ctx command state mid (protocolActions rest ++ tail) frame post hs ht

theorem protocol_wp [GS] (ctx : Context) (commands : List Bridge.Command) (state final : State) (frame : IProp GF)
    (hr : ByteAuthority.runCommands ctx.candidate ctx.histories ctx.cluster ctx.plan commands state = .ok final) :
    allPoints state ∗ frame ⊢ WP (script ctx (protocolActions commands))
      {{ value, ⌜value = .ok final⌝ ∗ allPoints final ∗ frame }} := by
  have hw := protocol_cps ctx commands state final [] frame _ hr (script_nil_all_wp ctx final frame)
  simpa only [List.append_nil] using hw

theorem protocol_adequate (ctx : Context) (commands : List Bridge.Command) (state final : State)
    (hr : ByteAuthority.runCommands ctx.candidate ctx.histories ctx.cluster ctx.plan commands state = .ok final) :
    adequate .NotStuck (script ctx (protocolActions commands)) state (fun value _ => value = .ok final) := by
  apply heap_adequacy
  intro _
  iintro Hall
  ihave Hwp := protocol_wp ctx commands state final iprop(True) hr $$ [$Hall]
  iapply wp_mono ?_ $$ Hwp
  intro value
  iintro ⟨%hv,Hall,Hframe⟩
  ipureintro; exact hv

theorem completed_protocol_run (ctx : Context) (commands : List Bridge.Command) (protocol final : Ptx.Async.State)
    (done : Cut) (bytes : HeapF ByteAuthority.Owner)
    (hc : Bridge.AllCompleted Tma.localShared ctx.candidate ctx.histories ctx.cluster ctx.plan done)
    (hr : Ptx.Async.run protocol (commands.map Bridge.Command.action) = .ok final) :
    IrisExecution.run (transition ctx) (protocolActions commands) ⟨⟨protocol,done⟩,bytes⟩ = .ok ⟨⟨final,done⟩,bytes⟩ := by
  rw [protocol_run]
  exact ByteAuthority.runCommands_succeeds hc commands hr bytes

theorem source_protocol_run (ctx : Context) (locations : List Location) (protocol final : Ptx.Async.State)
    (hb : ByteAuthority.Footprint.Bounded ctx.candidate locations) {before after nodes}
    (ho : ByteAuthority.Footprint.Ordered ctx.block ctx.candidate ctx.histories before nodes after)
    (commands : List Bridge.Command)
    (hc : Bridge.AllCompleted Tma.localShared ctx.candidate ctx.histories ctx.cluster ctx.plan after)
    (hr : Ptx.Async.run protocol (commands.map Bridge.Command.action) = .ok final) :
    IrisExecution.run (transition ctx) (sourceActions ctx locations nodes ++ protocolActions commands)
      (ByteAuthority.Footprint.initialized ⟨protocol,before⟩ locations) =
      .ok (ByteAuthority.Footprint.initialized ⟨final,after⟩ locations) := by
  rw [run_append,source_run ctx locations protocol hb ho]
  exact completed_protocol_run ctx commands protocol final after _ hc hr

theorem source_protocol_wp [GS] (ctx : Context) (locations : List Location) (protocol final : Ptx.Async.State)
    (hb : ByteAuthority.Footprint.Bounded ctx.candidate locations) {before after nodes}
    (ho : ByteAuthority.Footprint.Ordered ctx.block ctx.candidate ctx.histories before nodes after)
    (commands : List Bridge.Command)
    (hc : Bridge.AllCompleted Tma.localShared ctx.candidate ctx.histories ctx.cluster ctx.plan after)
    (hr : Ptx.Async.run protocol (commands.map Bridge.Command.action) = .ok final) (frame : IProp GF) :
    allPoints (ByteAuthority.Footprint.initialized ⟨protocol,before⟩ locations) ∗ frame ⊢
      WP (script ctx (sourceActions ctx locations nodes ++ protocolActions commands))
      {{ value, ⌜value = .ok (ByteAuthority.Footprint.initialized ⟨final,after⟩ locations)⌝ ∗
        allPoints (ByteAuthority.Footprint.initialized ⟨final,after⟩ locations) ∗ frame }} := by
  apply source_cps ctx locations protocol hb ho (protocolActions commands) frame _
  apply protocol_wp ctx commands _ _ frame
  exact ByteAuthority.runCommands_succeeds hc commands hr _

theorem source_protocol_adequate (ctx : Context) (locations : List Location) (protocol final : Ptx.Async.State)
    (hb : ByteAuthority.Footprint.Bounded ctx.candidate locations) {before after nodes}
    (ho : ByteAuthority.Footprint.Ordered ctx.block ctx.candidate ctx.histories before nodes after)
    (commands : List Bridge.Command)
    (hc : Bridge.AllCompleted Tma.localShared ctx.candidate ctx.histories ctx.cluster ctx.plan after)
    (hr : Ptx.Async.run protocol (commands.map Bridge.Command.action) = .ok final) :
    adequate .NotStuck (script ctx (sourceActions ctx locations nodes ++ protocolActions commands))
      (ByteAuthority.Footprint.initialized ⟨protocol,before⟩ locations)
      (fun value _ => value = .ok (ByteAuthority.Footprint.initialized ⟨final,after⟩ locations)) := by
  apply heap_adequacy
  intro _
  iintro Hall
  ihave Hwp := source_protocol_wp ctx locations protocol final hb ho commands hc hr iprop(True) $$ [$Hall]
  iapply wp_mono ?_ $$ Hwp
  intro value
  iintro ⟨%hv,Hall,Hframe⟩
  ipureintro; exact hv

/-- A rejected action preserves the current state and every framed resource;
there is no rollback assertion for earlier successful actions in a script. -/
theorem script_reject_wp [g : GS] (ctx : Context) (state : State) (action : Action) (tail : List Action)
    (error : ByteAuthority.Error) (frame : IProp GF) (hs : transition ctx action state = .error error) :
    control state ∗ frame ⊢ WP (script ctx (action::tail))
      {{ value, ⌜value = .error error⌝ ∗ control state ∗ frame }} := by
  let _ := g.inv
  iintro ⟨Hcontrol,Hframe⟩
  iapply wp_lift_atomic_step (show toVal (script ctx (action::tail)) = none from rfl)
  isimp [stateInterp]
  iintro %actual %ns %obs %obs' %nt Hheap
  ihave %heq : ⌜actual = state⌝ $$ [Hheap Hcontrol]
  · imod control_valid actual state $$ [$Hheap $Hcontrol] with %h
    ipureintro; exact h
  subst actual
  imodintro
  isplit
  · ipureintro
    exact ⟨[],IrisExecution.Expr.result (.error error),state,[],IrisExecution.Prim.abort hs⟩
  inext
  iintro %e' %actual %forks %hp Hcredit
  change IrisExecution.Prim (transition ctx) (.script (action::tail),state) obs (e',actual,forks) at hp
  cases hp with
  | next hnext => cases hs.symm.trans hnext
  | abort herr =>
    have he : error = _ := Except.error.inj (hs.symm.trans herr)
    subst he
    imodintro
    simp only [Iris.Algebra.BigOpL.bigOpL_nil]
    isplitl [Hheap]
    · iexact Hheap
    · isplitl [Hcontrol Hframe]
      · iexists (.error error)
        isplit
        · ipureintro; rfl
        · isplit
          · ipureintro; rfl
          · iframe Hcontrol Hframe
      · itrivial

theorem completed_protocol_error (ctx : Context) (commands : List Bridge.Command) (protocol : Ptx.Async.State)
    (done : Cut) (bytes : HeapF ByteAuthority.Owner) (error : Ptx.Async.Error)
    (hc : Bridge.AllCompleted Tma.localShared ctx.candidate ctx.histories ctx.cluster ctx.plan done)
    (hr : Ptx.Async.run protocol (commands.map Bridge.Command.action) = .error error) :
    IrisExecution.run (transition ctx) (protocolActions commands) ⟨⟨protocol,done⟩,bytes⟩ = .error (.protocolFailure error) := by
  rw [protocol_run]
  exact ByteAuthority.runCommands_error hc commands hr bytes

end
end Ptx.ByteAuthorityHeap
