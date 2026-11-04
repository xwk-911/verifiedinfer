import Ptx.Iris.HeapRules
import Ptx.Async.Shape
import Ptx.Async.Clients

/-! Protocol composition over the decomposed physical heap. Global acquire may
change loan metadata in several buffers, so this aggregate rule gathers actual
separated full location fragments. Local one-buffer rules remain available and
do not consume the aggregate or a whole-state OwnP fragment.
-/
namespace Ptx.AsyncHeap
noncomputable section
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation
open Iris.Std.LawfulSet
local bi (IProp GF)

theorem whole_action_wp [g : GS] {s action next} (hs : Async.step s action = .ok next) :
    allPoints s ⊢ WP (IrisAsync.Expr.invoke action) {{ v, ⌜v = .ok next⌝ ∗ allPoints next }} := by
  letI := g.inv
  iintro Hall
  iapply wp_lift_atomic_step (show toVal (IrisAsync.Expr.invoke action) = none from rfl)
  isimp [stateInterp]
  iintro %actual %ns %obs %obs' %nt Hheap
  ihave %heq : ⌜actual = s⌝ $$ [Hheap Hall]
  · imod allPoints_valid actual s $$ [$Hheap $Hall] with %h
    ipureintro; exact h
  subst actual
  imodintro
  isplit
  · ipureintro
    exact ⟨[],IrisExecution.Expr.result (.ok next),next,[],IrisExecution.Prim.success hs⟩
  inext
  iintro %e' %actual %forks %hp Hcredit
  obtain ⟨hstate,hval,hfork⟩ := IrisExecution.prim_deterministic hs hp
  simp only [IrisExecution.after] at hstate
  subst actual forks
  imod allPoints_update s next (Async.step_buffers_length hs).symm $$ [$Hheap $Hall]
    with ⟨Hheap,Hall⟩
  imodintro
  simp only [Iris.Algebra.BigOpL.bigOpL_nil]
  isplitl [Hheap]
  · iexact Hheap
  · isplitl [Hall]
    · iexists (.ok next)
      isplit
      · ipureintro; exact hval
      · isplit
        · ipureintro; trivial
        · iexact Hall
    · itrivial

theorem whole_script_wp [g : GS] {actions s final} (hs : Async.run s actions = .ok final) :
    allPoints s ⊢ WP (IrisAsync.Expr.script actions) {{ v, ⌜v = .ok final⌝ ∗ allPoints final }} := by
  letI := g.inv
  induction actions generalizing s with
  | nil =>
    simp only [Async.run,Except.ok.injEq] at hs
    subst final
    iintro Hall
    iapply wp_lift_atomic_step (show toVal (IrisAsync.Expr.script []) = none from rfl)
    isimp [stateInterp]
    iintro %actual %ns %obs %obs' %nt Hheap
    ihave %heq : ⌜actual = s⌝ $$ [Hheap Hall]
    · imod allPoints_valid actual s $$ [$Hheap $Hall] with %h
      ipureintro; exact h
    subst actual
    imodintro
    isplit
    · ipureintro
      exact ⟨[],IrisExecution.Expr.result (.ok s),s,[],IrisExecution.Prim.finish s⟩
    inext
    iintro %e' %actual %forks %hp Hcredit
    change IrisExecution.Prim IrisAsync.transition (.script [],s) obs (e',actual,forks) at hp
    cases hp
    imodintro
    simp only [Iris.Algebra.BigOpL.bigOpL_nil]
    isplitl [Hheap]
    · iexact Hheap
    · isplitl [Hall]
      · iexists (.ok s)
        isplit
        · ipureintro; rfl
        · isplit
          · ipureintro; trivial
          · iexact Hall
      · itrivial
  | cons action actions ih =>
    cases hstep : Async.step s action with
    | error e => simp [Async.run,hstep,Except.bind] at hs
    | ok next =>
      have hrest : Async.run next actions = .ok final := by simpa [Async.run,hstep,Except.bind] using hs
      iintro Hall
      iapply wp_lift_step (show toVal (IrisAsync.Expr.script (action::actions)) = none from rfl)
      isimp [stateInterp]
      iintro %actual %ns %obs %obs' %nt Hheap
      ihave %heq : ⌜actual = s⌝ $$ [Hheap Hall]
      · imod allPoints_valid actual s $$ [$Hheap $Hall] with %h
        ipureintro; exact h
      subst actual
      iapply fupd_mask_intro empty_subset
      iintro Hclose
      isplit
      · ipureintro
        exact ⟨[],IrisExecution.Expr.script actions,next,[],IrisExecution.Prim.next hstep⟩
      inext
      iintro %e' %actual %forks %hp Hcredit
      change IrisExecution.Prim IrisAsync.transition (.script (action::actions),s) obs (e',actual,forks) at hp
      cases hp with
      | next hnext =>
        have heq := Except.ok.inj (hstep.symm.trans hnext)
        subst actual
        imod allPoints_update s next (Async.step_buffers_length hstep).symm $$ [$Hheap $Hall]
          with ⟨Hheap,Hall⟩
        imod Hclose
        imodintro
        simp only [Iris.Algebra.BigOpL.bigOpL_nil]
        isplitl [Hheap]
        · iexact Hheap
        · isplitl [Hall]
          · iapply ih hrest $$ Hall
          · itrivial
      | abort herror => cases hstep.symm.trans herror

theorem whole_script_adequate {actions s final} (hs : Async.run s actions = .ok final) :
    adequate .NotStuck (IrisAsync.Expr.script actions) s (fun v _ => v = .ok final) := by
  apply heap_adequacy
  intro _
  refine (whole_script_wp hs).trans (wp_mono ?_)
  intro v
  iintro ⟨Hv,_⟩
  iexact Hv

/-- Both clients use the same decomposed physical interpretation and protocol WP.
Their lifetime proof for arbitrary finite action interleavings remains the shared
Async.Invariant theorem, separate from these client-specific value contracts. -/
theorem prefetch_heap_adequate (value : Nat) :
    adequate .NotStuck (IrisAsync.Expr.script Async.Contracts.prefetchActions) (Async.initial 2 [value,0])
      (fun v _ => v = .ok (Async.Contracts.prefetchFinal value)) :=
  whole_script_adequate (Async.Contracts.prefetch_exact value)

theorem deferred_heap_adequate (value : Nat) :
    adequate .NotStuck (IrisAsync.Expr.script Async.Contracts.deferredActions) (Async.initial 1 [value])
      (fun v _ => v = .ok (Async.Contracts.deferredFinal value)) :=
  whole_script_adequate (Async.Contracts.deferred_exact value)

/-- A real completed event returns the buffer fragment with exactly the loans
covered by its frontier removed. Other streams' and later loans remain in the
returned resource; this rule never replaces the filtered list with empty. -/
theorem acquire_buffer_wp [GS] (s : Async.State) (event bid : Nat) (ticket : Async.Ticket)
    (b : Async.Buffer) (he : Async.getEvent s event = .ok ticket)
    (hc : Async.complete s ticket = true) (hb : s.buffers[bid]? = some b) :
    allPoints s ⊢ WP (IrisAsync.Expr.invoke (.acquire event))
      {{ v, ⌜∃ next, v = .ok next⌝ ∗
        buffer bid (.own 1) {b with loans := b.loans.filter (fun l => !Async.covers ticket l.ticket)} }} := by
  let next : Async.State := {s with buffers := s.buffers.map (fun (old : Async.Buffer) =>
    {old with loans := old.loans.filter (fun l => !Async.covers ticket l.ticket)})}
  have hs : Async.step s (.acquire event) = .ok next := by
    simp [Async.step,Async.await,he,hc,next,bind,Except.bind,Pure.pure,Except.pure]
  have hnext : next.buffers[bid]? =
      some {b with loans := b.loans.filter (fun l => !Async.covers ticket l.ticket)} := by
    simp [next,List.getElem?_map,hb]
  refine (whole_action_wp hs).trans (wp_mono ?_)
  intro v
  iintro ⟨%hv,Hall⟩
  isplit
  · ipureintro; exact ⟨next,hv⟩
  · iapply allPoints_buffer hnext $$ Hall

/-- Universal reachable-state lifetime consequence through the initialized
physical heap, rather than through an assumed loan token or one sample trace. -/
theorem reachable_reclaim_heap_adequate {streams : Nat} {values : List Nat} {s : Async.State}
    {sid i bid : Nat} {st : Async.Stream} {cmd : Async.Command} {mode : Async.Mode}
    (hs : Async.Steps (Async.initial streams values) s) (hst : s.streams[sid]? = some st)
    (hcmd : st.queue[i]? = some cmd) (hacc : Async.Accesses cmd bid mode) :
    adequate .NotStuck (IrisAsync.Expr.invoke (.reclaim bid)) s
      (fun v _ => v = .error .outstandingLoan) := by
  have hi := Async.steps_invariant (Async.initial_invariant _ _) hs
  obtain ⟨b,hb,ha,hl⟩ := hi.pending sid st hst i cmd hcmd bid mode hacc
  have hnonempty : b.loans.isEmpty = false := by
    cases hloans : b.loans with
    | nil => simp [hloans] at hl
    | cons _ _ => rfl
  apply heap_adequacy
  intro _
  iintro Hall
  ihave Hb := allPoints_buffer hb $$ Hall
  ihave Hwp := reclaim_loan_reject_wp bid (.own 1) b ha hnonempty $$ Hb
  iapply wp_mono ?_ $$ Hwp
  intro v
  iintro ⟨Hv,_⟩
  iexact Hv

theorem reachable_write_heap_adequate {streams : Nat} {values : List Nat} {s : Async.State}
    {sid i bid value : Nat} {st : Async.Stream} {cmd : Async.Command} {mode : Async.Mode}
    (hs : Async.Steps (Async.initial streams values) s) (hst : s.streams[sid]? = some st)
    (hcmd : st.queue[i]? = some cmd) (hacc : Async.Accesses cmd bid mode) :
    adequate .NotStuck (IrisAsync.Expr.invoke (.write bid value)) s
      (fun v _ => v = .error .outstandingLoan) := by
  have hi := Async.steps_invariant (Async.initial_invariant _ _) hs
  obtain ⟨b,hb,ha,hl⟩ := hi.pending sid st hst i cmd hcmd bid mode hacc
  have hnonempty : b.loans.isEmpty = false := by
    cases hloans : b.loans with
    | nil => simp [hloans] at hl
    | cons _ _ => rfl
  apply heap_adequacy
  intro _
  iintro Hall
  ihave Hb := allPoints_buffer hb $$ Hall
  ihave Hwp := write_loan_reject_wp bid value (.own 1) b ha hnonempty $$ Hb
  iapply wp_mono ?_ $$ Hwp
  intro v
  iintro ⟨Hv,_⟩
  iexact Hv

/-- The full submit prefix followed by ANY finite legal finishing schedule has
the same exact result once queues and loans are drained. Schedule legality is
successful actual execution, not an assumption about the resulting data. -/
theorem prefetch_any_schedule_adequate (value : Nat) (actions : List Async.Client.PrefetchAction)
    {final : Async.State}
    (hs : Async.run (Async.Contracts.prefetchIssued value)
      (actions.map Async.Client.PrefetchAction.interpret) = .ok final)
    (hd : Async.Client.Drained final) (hr : Async.Client.Returned final) :
    adequate .NotStuck
      (IrisAsync.Expr.script (Async.Contracts.prefetchPrefix ++
        actions.map Async.Client.PrefetchAction.interpret)) (Async.initial 2 [value,0])
      (fun v _ => v = .ok (Async.Contracts.prefetchFinal value)) := by
  have heq := Async.Client.prefetch_finished (Async.Client.run_steps hs) hd hr
  apply whole_script_adequate
  rw [Async.Client.run_append,Async.Contracts.prefetch_issued]
  exact hs.trans (congrArg Except.ok heq)

theorem deferred_any_schedule_adequate (value : Nat) (actions : List Async.Client.DeferredAction)
    {final : Async.State}
    (hs : Async.run (Async.Contracts.deferredIssued value)
      (actions.map Async.Client.DeferredAction.interpret) = .ok final)
    (hf : final.buffers.all (fun b => !b.alive) = true) :
    adequate .NotStuck
      (IrisAsync.Expr.script (Async.Contracts.deferredPrefix ++
        actions.map Async.Client.DeferredAction.interpret)) (Async.initial 1 [value])
      (fun v _ => v = .ok (Async.Contracts.deferredFinal value)) := by
  have heq := Async.Client.deferred_finished (Async.Client.run_steps hs) hf
  apply whole_script_adequate
  rw [Async.Client.run_append,Async.Contracts.deferred_issued]
  exact hs.trans (congrArg Except.ok heq)

end
end Ptx.AsyncHeap
