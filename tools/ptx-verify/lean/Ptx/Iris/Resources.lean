import Ptx.Iris.Async

/-! Operational resource interface backed by Iris OwnP, replacing the old
unpreserved Represents premise and freely keyed capability heap. Every assertion
owns one exact whole physical state; claims for two buffers cannot duplicate it.
This is an exclusive engineering baseline, not fractional per-buffer composition.
The separate AsyncHeap interpretation provides actual buffer fragments and local
physical frame rules; this baseline is retained for comparison.
-/
namespace Ptx.Resources
noncomputable section
open Iris Iris.BI Iris.ProgramLogic
abbrev State := Async.State
noncomputable abbrev GF := IrisAsync.GF
abbrev ResourceAssertion := IProp GF
local bi ResourceAssertion

abbrev owns [OwnPGS State GF] (s : State) : ResourceAssertion := ownP s

def HostReady (s : State) (bid : Nat) : Prop :=
  ∃ b, Async.getBuffer s bid = .ok b ∧ b.loans.isEmpty = true

def host [OwnPGS State GF] (s : State) (bid : Nat) : ResourceAssertion :=
  iprop(⌜HostReady s bid⌝ ∗ owns s)

def valid [OwnPGS State GF] (s : State) : ResourceAssertion :=
  iprop(⌜Async.Invariant s⌝ ∗ owns s)

/-- Exact state fragments are exclusive, including across buffer labels. -/
theorem exclusive [OwnPGS State GF] (s t : State) : owns s ∗ owns t ⊢ False :=
  ownP_state_twice

theorem host_exclusive [OwnPGS State GF] (s t : State) (bid other : Nat) :
    host s bid ∗ host t other ⊢ False := by
  unfold host
  iintro ⟨⟨_, Hs⟩, ⟨_, Ht⟩⟩
  iapply exclusive s t $$ [$Hs $Ht]

/-- All actual successful actions consume and return the corresponding invariant
state resource. No separate, unproved realization preservation premise remains. -/
theorem action_rule [OwnPGS State GF] {s a s'} (hs : Async.step s a = .ok s') :
    valid s ⊢ WP (IrisAsync.Expr.invoke a) {{ v, ⌜v = .ok s'⌝ ∗ valid s' }} := by
  unfold valid owns
  iintro ⟨%hi, Hs⟩
  ihave Hwp := IrisAsync.invoke_invariant_wp hi hs $$ Hs
  iapply wp_mono ?_ $$ Hwp
  intro v
  iintro ⟨%hv, Hnext⟩
  obtain ⟨heq,hinv⟩ := hv
  subst v
  simp only [IrisExecution.after]
  isplit
  · ipureintro; trivial
  · isplit
    · ipureintro; exact hinv
    · iexact Hnext

/-- Host ownership now proves a real WP transition, not just existence under an
external Represents premise. The exact borrowed-state check is retained. -/
theorem reclaim_rule [OwnPGS State GF] {s bid} :
    host s bid ⊢ WP (IrisAsync.Expr.invoke (.reclaim bid))
      {{ v, ∃ s', ⌜v = .ok s'⌝ ∗ owns s' }} := by
  unfold host owns
  iintro ⟨%hr, Hs⟩
  obtain ⟨b,hb,hl⟩ := hr
  let next : State := { s with buffers := s.buffers.set bid { b with alive := false } }
  have hs : Async.step s (.reclaim bid) = .ok next := by
    simp [Async.step,Async.reclaim,hb,hl,next,bind,Except.bind,Pure.pure,Except.pure]
  ihave Hwp := IrisAsync.invoke_wp hs $$ Hs
  iapply wp_mono ?_ $$ Hwp
  intro v
  iintro ⟨%hv,Hnext⟩
  subst v
  simp only [IrisExecution.after]
  iexists next
  isplit
  · ipureintro; trivial
  · iexact Hnext

/-- Arbitrary frames are preserved by the actual Iris action WP. A frame is an
independent Iris resource, not a second physical fragment for an aliased buffer. -/
theorem frame_rule [OwnPGS State GF] {s a result}
    (hs : Async.step s a = result) (R : ResourceAssertion) :
    owns s ∗ R ⊢ WP (IrisAsync.Expr.invoke a)
      {{ v, R ∗ ⌜v = result⌝ ∗ owns (IrisExecution.after s v) }} :=
  IrisAsync.invoke_frame hs R

end
end Ptx.Resources
