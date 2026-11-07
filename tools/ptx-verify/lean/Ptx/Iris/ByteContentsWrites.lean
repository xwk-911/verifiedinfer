import Ptx.Iris.ByteContentsAvailable

/-! Values of actual unique writers persist after checked completion. This
links a completed source cut to final output cells without assuming an observer
value or treating the entire value script as one atomic transition.
-/
namespace Ptx.ByteContentsHeap
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def UniqueWrites (ctx : Context) (state : State) : Prop :=
  ∀ writer loc value, ByteContents.writeByte ctx.candidate writer loc = some value →
    (∀ other written, ByteContents.writeByte ctx.candidate other loc = some written → other = writer) →
    state.coupled.done (Unified.memoryControlNode writer) → ByteContents.valueAt state loc = some value

theorem unique_writes_initial {ctx : Context} {state : State} (hd : ∀ node, ¬state.coupled.done node) : UniqueWrites ctx state :=
  fun _ _ _ _ _ h => (hd _ h).elim

theorem unique_writes_action {ctx : Context} {action state next}
    (hi : UniqueWrites ctx state) (hs : transition ctx action state = .ok next) : UniqueWrites ctx next := by
  intro writer loc value hw hu hd
  cases action with
  | claim request =>
    rw [ByteContents.claim_preserves_value hs loc]
    rw [(ByteContents.claim_spec hs).choose_spec.2.2.1] at hd
    exact hi writer loc value hw hu hd
  | control node =>
    have hc := ByteContents.finishControl_spec hs
    rw [hc.2.1] at hd
    rcases hd with hd | hnew
    · rw [ByteContents.finishControl_preserves_value hs loc]
      exact hi writer loc value hw hu hd
    · have hn := (hc.1 writer hnew loc).2
      rw [hw] at hn
      cases hn
  | finish memory demands =>
    have hc := ByteContents.finish_spec hs
    rw [hc.2.2.1] at hd
    rcases hd with hd | hnew
    · have hn : ByteContents.writeByte ctx.candidate memory loc = none := by
        cases hm : ByteContents.writeByte ctx.candidate memory loc with
        | none => rfl
        | some written =>
          have he := hu memory written hm
          subst memory
          exact (hc.2.2.2.2.2.2.1 hd).elim
      rw [ByteContents.finish_preserves_unwritten hs hn]
      exact hi writer loc value hw hu hd
    · have he := hc.1.2 writer hnew ⟨loc,value,Or.inr hw⟩
      subst writer
      exact ByteContents.finish_writes_byte hs hw

theorem unique_writes_run (ctx : Context) (actions : List Action) {state next}
    (hi : UniqueWrites ctx state) (hr : IrisExecution.run (transition ctx) actions state = .ok next) : UniqueWrites ctx next := by
  induction actions generalizing state with
  | nil => cases hr; exact hi
  | cons head rest ih =>
    change (transition ctx head state).bind (fun mid => IrisExecution.run (transition ctx) rest mid) = .ok next at hr
    cases hs : transition ctx head state with
    | error error => simp [hs,Except.bind] at hr
    | ok mid => exact ih (unique_writes_action hi hs) (by simpa only [hs,Except.bind] using hr)

end
end Ptx.ByteContentsHeap
