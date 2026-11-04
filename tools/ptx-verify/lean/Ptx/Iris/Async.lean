import Ptx.Async.Contracts
import Ptx.Iris.Execution

/-! Actual async actions instantiate the checked Iris language. Scripts take one
action per primitive step. OwnP supplies whole-state ownership; per-buffer resource
splitting and PTX completion refinement are separate, not assumed here. -/
namespace Ptx.IrisAsync
open Iris Iris.BI Iris.ProgramLogic

abbrev State := Async.State
abbrev Outcome := Except Async.Error State
def transition (a : Async.Action) (s : State) : Outcome := Async.step s a
abbrev Expr := IrisExecution.Expr transition
abbrev Expr.invoke (a : Async.Action) : Expr := IrisExecution.Expr.invoke a
abbrev Expr.script (actions : List Async.Action) : Expr := IrisExecution.Expr.script actions
noncomputable abbrev GF := IrisExecution.GF State
local bi (IProp GF)

theorem invoke_wp [OwnPGS State GF] {s a r} (hs : Async.step s a = r) :
    ownP (GF := GF) s ⊢ WP (Expr.invoke a)
      {{ v, ⌜v = r⌝ ∗ ownP (IrisExecution.after s v) }} :=
  IrisExecution.invoke_wp hs

theorem invoke_frame [OwnPGS State GF] {s a r} (hs : Async.step s a = r)
    (R : IProp GF) :
    ownP (GF := GF) s ∗ R ⊢ WP (Expr.invoke a)
      {{ v, R ∗ ⌜v = r⌝ ∗ ownP (IrisExecution.after s v) }} :=
  IrisExecution.invoke_frame hs R

theorem invoke_invariant_wp [OwnPGS State GF] {s a s'}
    (hi : Async.Invariant s) (hs : Async.step s a = .ok s') :
    ownP (GF := GF) s ⊢ WP (Expr.invoke a)
      {{ v, ⌜v = .ok s' ∧ Async.Invariant s'⌝ ∗ ownP (IrisExecution.after s v) }} := by
  refine (invoke_wp hs).trans (wp_mono ?_)
  intro v
  iintro ⟨%hv, Hs⟩
  isplit
  · ipureintro; exact ⟨hv, Async.step_invariant hi hs⟩
  · iexact Hs

theorem invoke_adequate {s a r} (hs : Async.step s a = r) :
    adequate .NotStuck (Expr.invoke a) s (fun v _ => v = r) :=
  IrisExecution.invoke_adequate hs

theorem run_eq (actions : List Async.Action) (s : State) :
    IrisExecution.run transition actions s = Async.run s actions := by
  induction actions generalizing s with
  | nil => rfl
  | cons a actions ih =>
    cases h : Async.step s a <;>
      simp [IrisExecution.run,Async.run,transition,h,Except.bind,ih]

theorem script_wp [OwnPGS State GF] {actions s s'} (hs : Async.run s actions = .ok s') :
    ownP (GF := GF) s ⊢ WP (Expr.script actions) {{ v, ⌜v = .ok s'⌝ ∗ ownP s' }} :=
  IrisExecution.script_wp ((run_eq actions s).trans hs)

theorem script_adequate {actions s s'} (hs : Async.run s actions = .ok s') :
    adequate .NotStuck (Expr.script actions) s (fun v _ => v = .ok s') :=
  IrisExecution.script_adequate ((run_eq actions s).trans hs)

theorem prefetch_adequate (value : Nat) :
    adequate .NotStuck (Expr.script Async.Contracts.prefetchActions) (Async.initial 2 [value,0])
      (fun v _ => v = .ok (Async.Contracts.prefetchFinal value)) :=
  script_adequate (Async.Contracts.prefetch_exact value)

theorem deferred_adequate (value : Nat) :
    adequate .NotStuck (Expr.script Async.Contracts.deferredActions) (Async.initial 1 [value])
      (fun v _ => v = .ok (Async.Contracts.deferredFinal value)) :=
  script_adequate (Async.Contracts.deferred_exact value)

/-- A queued access justifies a rejection contract, never successful reclaim. -/
theorem pending_reclaim_wp [OwnPGS State GF] {s : State} {sid i bid : Nat}
    {st : Async.Stream} {cmd : Async.Command} {mode : Async.Mode}
    (hi : Async.Invariant s) (hst : s.streams[sid]? = some st)
    (hcmd : st.queue[i]? = some cmd) (hacc : Async.Accesses cmd bid mode) :
    ownP (GF := GF) s ⊢ WP (Expr.invoke (.reclaim bid))
      {{ v, ⌜v = .error .outstandingLoan⌝ ∗ ownP (IrisExecution.after s v) }} :=
  invoke_wp (Async.pending_reclaim_rejected hi hst hcmd hacc)

theorem pending_reclaim_adequate {s : State} {sid i bid : Nat}
    {st : Async.Stream} {cmd : Async.Command} {mode : Async.Mode}
    (hi : Async.Invariant s) (hst : s.streams[sid]? = some st)
    (hcmd : st.queue[i]? = some cmd) (hacc : Async.Accesses cmd bid mode) :
    adequate .NotStuck (Expr.invoke (.reclaim bid)) s (fun v _ => v = .error .outstandingLoan) :=
  invoke_adequate (Async.pending_reclaim_rejected hi hst hcmd hacc)

theorem reject_not_ok_adequate {actions s error} (hs : Async.run s actions = .error error) :
    ¬ adequate .NotStuck (Expr.script actions) s (fun v _ => ∃ s', v = .ok s') :=
  IrisExecution.script_reject_not_ok_adequate ((run_eq actions s).trans hs)

end Ptx.IrisAsync
