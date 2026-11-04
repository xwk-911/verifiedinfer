import Ptx.Iris.Heap

/-! Local WP rules for real async actions with physical buffer fragments.
The footprint premise is an ordinary proved transition property, not an axiom.
The public reclaim/write rules below discharge it from the concrete interpreter.
-/
namespace Ptx.AsyncHeap
noncomputable section
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation
open Iris.Std.PartialMap
local bi (IProp GF)

/-- A physical one-buffer footprint rule. All unrelated buffer/control fragments
can be framed by Iris; the precondition contains no whole-state OwnP fragment. -/
theorem buffer_action_wp [g : GS] (a : Async.Action) (bid : Nat) (old fresh : Async.Buffer)
    (law : ∀ s : Async.State, s.buffers[bid]? = some old →
      ∃ next, Async.step s a = .ok next ∧
        store next = insert (store s) (bid+1) (.buffer fresh)) :
    buffer bid (.own 1) old ⊢ WP (IrisAsync.Expr.invoke a)
      {{ v, ⌜∃ next, v = .ok next⌝ ∗ buffer bid (.own 1) fresh }} := by
  letI := g.inv
  iintro Hb
  iapply wp_lift_atomic_step (show toVal (IrisAsync.Expr.invoke a) = none from rfl)
  isimp [stateInterp]
  iintro %s %ns %obs %obs' %nt Hheap
  ihave %hget : ⌜s.buffers[bid]? = some old⌝ $$ [Hheap Hb]
  · imod buffer_valid s bid (.own 1) old $$ [$Hheap $Hb] with %h
    ipureintro; exact h
  obtain ⟨next,hs,hstore⟩ := law s hget
  imodintro
  isplit
  · ipureintro
    exact ⟨[],IrisExecution.Expr.result (.ok next),next,[],IrisExecution.Prim.success hs⟩
  inext
  iintro %e' %s' %ef %hp Hcred
  obtain ⟨hstate,hval,hfork⟩ := IrisExecution.prim_deterministic hs hp
  simp only [IrisExecution.after] at hstate
  subst s' ef
  unfold buffer
  imod genHeap_update (v₂ := Cell.buffer fresh) $$ [$Hheap $Hb] with ⟨Hheap,Hb⟩
  rw [← hstore]
  imodintro
  simp only [Iris.Algebra.BigOpL.bigOpL_nil]
  isplitl [Hheap]
  · iexact Hheap
  · isplitl [Hb]
    · iexists (.ok next)
      isplit
      · ipureintro; exact hval
      · isplit
        · ipureintro; exact ⟨next,rfl⟩
        · iexact Hb
    · itrivial

theorem reclaim_local_wp [GS] (bid : Nat) (b : Async.Buffer)
    (ha : b.alive = true) (hl : b.loans.isEmpty = true) :
    buffer bid (.own 1) b ⊢ WP (IrisAsync.Expr.invoke (.reclaim bid))
      {{ v, ⌜∃ next, v = .ok next⌝ ∗ buffer bid (.own 1) {b with alive := false} }} := by
  apply buffer_action_wp
  intro s hget
  have hb := Async.getBuffer_iff.mpr ⟨hget,ha⟩
  let next := {s with buffers := s.buffers.set bid {b with alive := false}}
  refine ⟨next,?_,?_⟩
  · simp [Async.step,Async.reclaim,hb,hl,next,bind,Except.bind,Pure.pure,Except.pure]
  · exact store_set_buffer (List.getElem?_eq_some_iff.mp hget).1

theorem write_local_wp [GS] (bid value : Nat) (b : Async.Buffer)
    (ha : b.alive = true) (hl : b.loans.isEmpty = true) :
    buffer bid (.own 1) b ⊢ WP (IrisAsync.Expr.invoke (.write bid value))
      {{ v, ⌜∃ next, v = .ok next⌝ ∗ buffer bid (.own 1) {b with value := value} }} := by
  apply buffer_action_wp
  intro s hget
  have hb := Async.getBuffer_iff.mpr ⟨hget,ha⟩
  let next := {s with buffers := s.buffers.set bid {b with value := value}}
  refine ⟨next,?_,?_⟩
  · simp [Async.step,Async.hostWrite,hb,hl,next,bind,Except.bind,Pure.pure,Except.pure]
  · exact store_set_buffer (List.getElem?_eq_some_iff.mp hget).1

theorem reclaim_frame_buffer [GS] (bid other : Nat) (b frame : Async.Buffer) (dq : DFrac)
    (ha : b.alive = true) (hl : b.loans.isEmpty = true) :
    buffer bid (.own 1) b ∗ buffer other dq frame ⊢
      WP (IrisAsync.Expr.invoke (.reclaim bid))
        {{ v, buffer other dq frame ∗ ⌜∃ next, v = .ok next⌝ ∗
          buffer bid (.own 1) {b with alive := false} }} := by
  iintro ⟨Hb,Hframe⟩
  iapply wp_frame_r
  isplitl [Hb]
  · iapply reclaim_local_wp bid b ha hl $$ Hb
  · iexact Hframe

/-- A read-only physical snapshot suffices to prove a real rejection. No full
write ownership is consumed, since this action leaves the physical state alone. -/
theorem buffer_reject_wp [g : GS] (a : Async.Action) (bid : Nat) (dq : DFrac)
    (b : Async.Buffer) (error : Async.Error)
    (law : ∀ s : Async.State, s.buffers[bid]? = some b → Async.step s a = .error error) :
    buffer bid dq b ⊢ WP (IrisAsync.Expr.invoke a)
      {{ v, ⌜v = .error error⌝ ∗ buffer bid dq b }} := by
  letI := g.inv
  iintro Hb
  iapply wp_lift_atomic_step (show toVal (IrisAsync.Expr.invoke a) = none from rfl)
  isimp [stateInterp]
  iintro %s %ns %obs %obs' %nt Hheap
  ihave %hget : ⌜s.buffers[bid]? = some b⌝ $$ [Hheap Hb]
  · imod buffer_valid s bid dq b $$ [$Hheap $Hb] with %h
    ipureintro; exact h
  have hs := law s hget
  imodintro
  isplit
  · ipureintro
    exact ⟨[],IrisExecution.Expr.result (.error error),s,[],IrisExecution.Prim.reject hs⟩
  inext
  iintro %e' %s' %ef %hp Hcred
  obtain ⟨hstate,hval,hfork⟩ := IrisExecution.prim_deterministic hs hp
  simp only [IrisExecution.after] at hstate
  subst s' ef
  imodintro
  simp only [Iris.Algebra.BigOpL.bigOpL_nil]
  isplitl [Hheap]
  · iexact Hheap
  · isplitl [Hb]
    · iexists (.error error)
      isplit
      · ipureintro; exact hval
      · isplit
        · ipureintro; trivial
        · iexact Hb
    · itrivial

theorem reclaim_loan_reject_wp [GS] (bid : Nat) (dq : DFrac) (b : Async.Buffer)
    (ha : b.alive = true) (hl : b.loans.isEmpty = false) :
    buffer bid dq b ⊢ WP (IrisAsync.Expr.invoke (.reclaim bid))
      {{ v, ⌜v = .error .outstandingLoan⌝ ∗ buffer bid dq b }} := by
  apply buffer_reject_wp
  intro s hget
  exact Async.reclaim_rejects_loan (Async.getBuffer_iff.mpr ⟨hget,ha⟩) hl

theorem write_loan_reject_wp [GS] (bid value : Nat) (dq : DFrac) (b : Async.Buffer)
    (ha : b.alive = true) (hl : b.loans.isEmpty = false) :
    buffer bid dq b ⊢ WP (IrisAsync.Expr.invoke (.write bid value))
      {{ v, ⌜v = .error .outstandingLoan⌝ ∗ buffer bid dq b }} := by
  apply buffer_reject_wp
  intro s hget
  have hb := Async.getBuffer_iff.mpr ⟨hget,ha⟩
  simp [Async.step,Async.hostWrite,hb,hl,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

/-- Both read halves are realized by the actual pending buffer. The failed
reclaim keeps both halves, while a full write token cannot coexist with either. -/
theorem split_reader_reject_adequate (value : Nat) :
    adequate .NotStuck (IrisAsync.Expr.invoke (.reclaim 0)) (Async.Contracts.deferredIssued value)
      (fun v _ => v = .error .outstandingLoan) := by
  apply heap_adequacy
  intro _
  let b : Async.Buffer := {value := value,loans := [⟨⟨0,1⟩,.read⟩] }
  have hb : (Async.Contracts.deferredIssued value).buffers[0]? = some b := rfl
  iintro Hall
  ihave Hb := allPoints_buffer hb $$ Hall
  icases (buffer_split 0 1 b).mp $$ Hb with ⟨Hleft,Hright⟩
  ihave Hframed : iprop(WP (IrisAsync.Expr.invoke (.reclaim 0))
      {{ v, buffer 0 (.own (1 : Qp).half) b ∗ ⌜v = .error .outstandingLoan⌝ ∗
        buffer 0 (.own (1 : Qp).half) b }}) $$ [Hleft Hright]
  · iapply wp_frame_r
    isplitl [Hleft]
    · iapply reclaim_loan_reject_wp 0 (.own (1 : Qp).half) b rfl rfl $$ Hleft
    · iexact Hright
  iapply wp_mono ?_ $$ Hframed
  intro v
  iintro ⟨_,Hv,_⟩
  iexact Hv

/-- This closed family has a real initialized witness for a framed physical
reclaim: two distinct live buffers, arbitrary data, no free GS assumptions. -/
theorem framed_reclaim_adequate (value other : Nat) :
    adequate .NotStuck (IrisAsync.Expr.invoke (.reclaim 0)) (Async.initial 1 [value,other])
      (fun v _ => ∃ next, v = .ok next) := by
  apply heap_adequacy
  intro _
  iintro Hall
  unfold allPoints
  icases (BigSepM.bigSepM_delete (store_buffer (Async.initial 1 [value,other]) 0))
    $$ Hall with ⟨Hb,Hrest⟩
  have hother : get? (Iris.Std.PartialMap.delete (store (Async.initial 1 [value,other])) 1) 2 =
      some (.buffer {value := other}) := by
    rw [Iris.Std.LawfulPartialMap.get?_delete_ne (by decide : 1 ≠ 2)]
    exact store_buffer (Async.initial 1 [value,other]) 1
  ihave Hframe := BigSepM.bigSepM_lookup hother $$ Hrest
  ihave HbLocal : buffer 0 (.own 1) {value := value} $$ [Hb]
  · unfold buffer
    iexact Hb
  ihave HframeLocal : buffer 1 (.own 1) {value := other} $$ [Hframe]
  · unfold buffer
    iexact Hframe
  ihave Hwp := reclaim_frame_buffer 0 1 {value := value} {value := other} (.own 1)
    rfl rfl $$ [$HbLocal $HframeLocal]
  iapply wp_mono ?_ $$ Hwp
  intro v
  iintro ⟨_,Hv,_⟩
  iexact Hv

end
end Ptx.AsyncHeap
