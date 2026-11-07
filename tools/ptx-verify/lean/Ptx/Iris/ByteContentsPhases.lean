import Ptx.Iris.ByteContentsFootprint
import Ptx.Hopper.ByteContentsPhases

/-! Phase-order preservation across actual successful value scripts. Other
writers are excluded by closed source cuts and real completion/freshness, not
by a caller-supplied no-clobber premise or a total order on all memory events.
-/
namespace Ptx.ByteContentsHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def PhaseOrder (ctx : Context) (producer reader : Unified.Node) (loc : Location) : Prop :=
  ∀ other value, ByteContents.writeByte ctx.candidate other loc = some value →
    other = producer ∨
      Ptx.Event.Path (Unified.ControlEdge ctx.block ctx.candidate ctx.histories)
        (Unified.memoryControlNode other) (Unified.memoryControlNode producer) ∨
      Ptx.Event.Path (Unified.ControlEdge ctx.block ctx.candidate ctx.histories)
        (Unified.memoryControlNode reader) (Unified.memoryControlNode other)

theorem phase_of_byte_order {ctx : Context} {cluster producer reader loc}
    (hn : ∀ id, Access.copyAt ctx.candidate.view id = none)
    (hp : ∀ other value, ByteContents.writeByte ctx.candidate other loc = some value →
      other = producer ∨ Unified.ByteOrder Tma.localShared Access.globalDescriptor ctx.candidate ctx.histories cluster loc other producer ∨
        Unified.ByteOrder Tma.localShared Access.globalDescriptor ctx.candidate ctx.histories cluster loc reader other) :
    PhaseOrder ctx producer reader loc := by
  intro other value hw
  rcases hp other value hw with he | hbefore | hafter
  · exact Or.inl he
  · exact Or.inr (Or.inl (Unified.byte_order_control_path hn hbefore))
  · exact Or.inr (Or.inr (Unified.byte_order_control_path hn hafter))

theorem action_done_monotone (ctx : Context) {action state next}
    (hs : transition ctx action state = .ok next) : ∀ node, state.coupled.done node → next.coupled.done node := by
  cases action with
  | claim request =>
    obtain ⟨old,_,_,rfl,_⟩ := ByteContents.claim_spec hs
    exact fun _ h => h
  | control node =>
    rw [(ByteContents.finishControl_spec hs).2.1]
    exact fun _ h => Or.inl h
  | finish memory demands =>
    rw [(ByteContents.finish_spec hs).2.2.1]
    exact fun _ h => Or.inl h

theorem run_done_monotone (ctx : Context) (actions : List Action) {state next}
    (hr : IrisExecution.run (transition ctx) actions state = .ok next) : ∀ node, state.coupled.done node → next.coupled.done node := by
  induction actions generalizing state with
  | nil => cases hr; exact fun _ h => h
  | cons head rest ih =>
    change (transition ctx head state).bind (fun mid => IrisExecution.run (transition ctx) rest mid) = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid =>
      have ht := ih (by simpa only [hs,Except.bind] using hr)
      exact fun node hd => ht node (action_done_monotone ctx hs node hd)

theorem action_valid (ctx : Context) {action state next}
    (hv : Valid ctx.block ctx.candidate ctx.histories state.coupled.done)
    (hs : transition ctx action state = .ok next) : Valid ctx.block ctx.candidate ctx.histories next.coupled.done := by
  cases action with
  | claim request =>
    obtain ⟨old,_,_,rfl,_⟩ := ByteContents.claim_spec hs
    exact hv
  | control node =>
    have hf := ByteContents.finishControl_spec hs
    rw [hf.2.1]
    exact advance_valid hv (.next _ hf.2.2.1.1 hf.2.2.1.2.1 hf.2.2.1.2.2)
  | finish memory demands =>
    have hf := ByteContents.finish_spec hs
    rw [hf.2.2.1]
    exact advance_valid hv (.next _ hf.2.2.2.2.2.1 hf.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2)

theorem run_valid (ctx : Context) (actions : List Action) {state next}
    (hv : Valid ctx.block ctx.candidate ctx.histories state.coupled.done)
    (hr : IrisExecution.run (transition ctx) actions state = .ok next) :
    Valid ctx.block ctx.candidate ctx.histories next.coupled.done := by
  induction actions generalizing state with
  | nil => cases hr; exact hv
  | cons head rest ih =>
    change (transition ctx head state).bind (fun mid => IrisExecution.run (transition ctx) rest mid) = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid => exact ih (action_valid ctx hv hs) (by simpa only [hs,Except.bind] using hr)

theorem action_preserves_phase (ctx : Context) {action state next producer reader loc}
    (hv : Valid ctx.block ctx.candidate ctx.histories state.coupled.done)
    (hd : state.coupled.done (Unified.memoryControlNode producer))
    (hp : ¬next.coupled.done (Unified.memoryControlNode reader))
    (hphase : PhaseOrder ctx producer reader loc) (hs : transition ctx action state = .ok next) :
    ByteContents.valueAt next loc = ByteContents.valueAt state loc := by
  cases action with
  | claim request => exact ByteContents.claim_preserves_value hs loc
  | control node => exact ByteContents.finishControl_preserves_value hs loc
  | finish writer demands =>
    have hf := ByteContents.finish_spec hs
    have hready := hf.2.2.2.2.2
    have hvalid := action_valid ctx hv hs
    have hn : ByteContents.writeByte ctx.candidate writer loc = none := by
      cases hw : ByteContents.writeByte ctx.candidate writer loc with
      | none => rfl
      | some value =>
        rcases hphase writer value hw with rfl | hbefore | hafter
        · exact (hready.2.1 hd).elim
        · exact (hready.2.1 (closed_path hv.1 hbefore hd)).elim
        · have hwDone : next.coupled.done (Unified.memoryControlNode writer) := by rw [hf.2.2.1]; exact Or.inr rfl
          exact (hp (closed_path hvalid.1 hafter hwDone)).elim
    exact ByteContents.finish_preserves_unwritten hs hn

theorem run_preserves_phase (ctx : Context) (actions : List Action) {state next producer reader loc}
    (hv : Valid ctx.block ctx.candidate ctx.histories state.coupled.done)
    (hd : state.coupled.done (Unified.memoryControlNode producer))
    (hp : ¬next.coupled.done (Unified.memoryControlNode reader))
    (hphase : PhaseOrder ctx producer reader loc) (hr : IrisExecution.run (transition ctx) actions state = .ok next) :
    ByteContents.valueAt next loc = ByteContents.valueAt state loc := by
  induction actions generalizing state with
  | nil => cases hr; rfl
  | cons head rest ih =>
    change (transition ctx head state).bind (fun mid => IrisExecution.run (transition ctx) rest mid) = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid =>
      have ht : IrisExecution.run (transition ctx) rest mid = .ok next := by simpa only [hs,Except.bind] using hr
      have hm : ¬mid.coupled.done (Unified.memoryControlNode reader) := fun h => hp (run_done_monotone ctx rest ht _ h)
      exact (ih (action_valid ctx hv hs) (action_done_monotone ctx hs _ hd) ht).trans
        (action_preserves_phase ctx hv hd hm hphase hs)

theorem producer_to_reader_view (ctx : Context) (actions : List Action)
    {before written ready : State} {producer reader : Unified.Node} {loc : Location} {value : Symbolic.Byte} {demands : List Demand}
    {initial : Unified.ProxyMemory} {rf : Unified.ReadsFrom}
    (hv : Valid ctx.block ctx.candidate ctx.histories before.coupled.done)
    (hw : transition ctx (.finish producer demands) before = .ok written)
    (hwrite : ByteContents.writeByte ctx.candidate producer loc = some value)
    (hr : IrisExecution.run (transition ctx) actions written = .ok ready)
    (hp : ¬ready.coupled.done (Unified.memoryControlNode reader))
    (hphase : PhaseOrder ctx producer reader loc) (hrf : rf reader loc = some producer) :
    ByteContents.valueAt ready loc = Unified.sourceValue Tma.localShared Access.globalDescriptor ctx.candidate initial reader loc (rf reader loc) := by
  have hf := ByteContents.finish_spec hw
  have hd : written.coupled.done (Unified.memoryControlNode producer) := by rw [hf.2.2.1]; exact Or.inr rfl
  rw [run_preserves_phase ctx actions (action_valid ctx hv hw) hd hp hphase hr]
  exact ByteContents.finish_realizes_selected_write hw hwrite hrf

end
end Ptx.ByteContentsHeap
