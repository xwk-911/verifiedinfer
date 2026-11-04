import Iris.ProgramLogic.OwnP
import Iris.Algebra.Auth

/-! A reusable Iris language for an executable, fallible state transition.
Each invocation is one physical transition; scripts take one transition per action,
not one atomic transition for the whole script. Errors are explicit return values.
The resource interpretation is OwnP's authoritative/exclusive whole physical state.
It deliberately does not claim per-location physical ownership or fork rules.
-/
namespace Ptx.IrisExecution
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language
open Iris.ProgramLogic.Language.Notation

variable {Action Error State : Type}

abbrev Outcome (Error State : Type) := Except Error State

inductive Expr (transition : Action → State → Outcome Error State) where
  | invoke (action : Action)
  | script (actions : List Action)
  | result (value : Outcome Error State)

def after (s : State) : Outcome Error State → State
  | .ok s' => s'
  | .error _ => s

inductive Prim (transition : Action → State → Outcome Error State) :
    Expr transition × State → List Unit → Expr transition × State × List (Expr transition) → Prop where
  | success {s a s'} (h : transition a s = .ok s') :
      Prim transition (.invoke a,s) [] (.result (.ok s'),s',[])
  | reject {s a e} (h : transition a s = .error e) :
      Prim transition (.invoke a,s) [] (.result (.error e),s,[])
  | finish (s) : Prim transition (.script [],s) [] (.result (.ok s),s,[])
  | next {s a actions s'} (h : transition a s = .ok s') :
      Prim transition (.script (a::actions),s) [] (.script actions,s',[])
  | abort {s a actions e} (h : transition a s = .error e) :
      Prim transition (.script (a::actions),s) [] (.result (.error e),s,[])

instance (transition : Action → State → Outcome Error State) :
    Language (Expr transition) State Unit (Outcome Error State) where
  toVal := fun e => match e with | .result v => some v | _ => none
  ofVal := Expr.result
  coe_of_toVal_eq_some := by intro e v h; cases e <;> simp_all
  toVal_coe := by intro v; rfl
  primStep := Prim transition
  val_stuck := by intro e s obs e' s' ef h; cases h <;> rfl

variable {transition : Action → State → Outcome Error State}

theorem reducible (s : State) (a : Action) :
    PrimStep.Reducible (Expr.invoke (transition := transition) a,s) := by
  cases h : transition a s with
  | ok s' => exact ⟨[],Expr.result (.ok s'),s',[],Prim.success h⟩
  | error e => exact ⟨[],Expr.result (.error e),s,[],Prim.reject h⟩

theorem prim_deterministic {s a r} (hs : transition a s = r)
    {obs : List Unit} {e' : Expr transition} {s' : State} {ef : List (Expr transition)}
    (hp : (Expr.invoke a,s) -<obs>-> (e',s',ef)) :
    s' = after s r ∧ toVal e' = some r ∧ ef = [] := by
  change Prim transition (.invoke a,s) obs (e',s',ef) at hp
  cases hp with
  | success h =>
    have heq := hs.symm.trans h
    rw [heq]
    exact ⟨rfl,rfl,rfl⟩
  | reject h =>
    have heq := hs.symm.trans h
    rw [heq]
    exact ⟨rfl,rfl,rfl⟩

open COFE Auth Std.LawfulSet
/-- Concrete closed family, including invariant bookkeeping and later credits. -/
noncomputable def GF (S : Type) : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF⟩
  | 1 => ⟨constOF CoPsetDisjL⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet)⟩
  | 3 => ⟨AuthURF (constOF Credit)⟩
  | 4 => ⟨ownPRF S⟩
  | _ => ⟨constOF Unit⟩

instance (S : Type) : WsatGpreS (GF S) where
  inv := {τ := 0,transp := by unfold GF; rfl}
  enabled := {τ := 1,transp := by unfold GF; rfl}
  disabled := {τ := 2,transp := by unfold GF; rfl}
instance (S : Type) : LcGpreS (GF S) where
  lc_elem := {τ := 3,transp := by unfold GF; rfl}
instance (S : Type) : InvGpreS (GF S) where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance
instance (S : Type) : OwnPGpreS S (GF S) where
  toInvGpreS := inferInstance
  inG := {τ := 4,transp := by unfold GF; rfl}

local bi (IProp (GF State))

theorem invoke_wp [OwnPGS State (GF State)] {s a r} (hs : transition a s = r) :
    ownP (GF := GF State) s ⊢
      WP (Expr.invoke (transition := transition) a) {{ v, ⌜v = r⌝ ∗ ownP (after s v) }} := by
  iintro Hs
  iapply ownP_lift_atomic_det_step (eₜ := []) (v₂ := r)
    (σ₁ := s) (σ₂ := after s r) (s := .NotStuck) (reducible s a) (fun hp => prim_deterministic hs hp)
  isplitl [Hs]
  · inext
    iexact Hs
  · inext
    iintro Hnext
    simp only [Iris.Algebra.BigOpL.bigOpL_nil]
    isplitl [Hnext]
    · isplit
      · ipureintro; trivial
      · iexact Hnext
    · itrivial

/-- Frames arbitrary independent Iris resources, without splitting OwnP. -/
theorem invoke_frame [OwnPGS State (GF State)] {s a r} (hs : transition a s = r)
    (R : IProp (GF State)) :
    ownP (GF := GF State) s ∗ R ⊢ WP (Expr.invoke (transition := transition) a)
      {{ v, R ∗ ⌜v = r⌝ ∗ ownP (after s v) }} := by
  iintro ⟨Hs, HR⟩
  iapply wp_frame_r
  isplitl [Hs]
  · iapply invoke_wp hs $$ Hs
  · iexact HR

theorem invoke_adequate {s a r} (hs : transition a s = r) :
    adequate .NotStuck (Expr.invoke (transition := transition) a) s (fun v _ => v = r) := by
  apply ownP_adequacy (GF := GF State) .NotStuck (Expr.invoke a) s (fun v => v = r)
  intro _
  refine (invoke_wp hs).trans (wp_mono ?_)
  intro v
  iintro ⟨Hv, _⟩
  iexact Hv

def run (transition : Action → State → Outcome Error State) :
    List Action → State → Outcome Error State
  | [], s => .ok s
  | a::actions, s => (transition a s).bind (run transition actions)

/-- Successful scripts use the non-atomic, one-action-per-step language above.
No executable error can establish this successful-result postcondition. -/
theorem script_wp [ι : OwnPGS State (GF State)] {actions s s'}
    (hs : run transition actions s = .ok s') :
    ownP (GF := GF State) s ⊢ WP (Expr.script (transition := transition) actions)
      {{ v, ⌜v = .ok s'⌝ ∗ ownP s' }} := by
  letI : InvGS (GF State) := ι.invGS
  induction actions generalizing s with
  | nil =>
    simp only [run, Except.ok.injEq] at hs
    subst s'
    iintro Hs
    iapply ownP_lift_atomic_det_step (eₜ := []) (v₂ := .ok s)
      (σ₁ := s) (σ₂ := s) (s := .NotStuck)
      (show PrimStep.Reducible (Expr.script (transition := transition) [],s) from
        ⟨[],Expr.result (.ok s),s,[],Prim.finish s⟩) ?_
    · intro obs e' next ef hp
      change Prim transition (.script [],s) obs (e',next,ef) at hp
      cases hp
      exact ⟨rfl,rfl,rfl⟩
    · isplitl [Hs]
      · inext; iexact Hs
      · inext
        iintro Hnext
        simp only [Iris.Algebra.BigOpL.bigOpL_nil]
        isplitl [Hnext]
        · isplit
          · ipureintro; trivial
          · iexact Hnext
        · itrivial
  | cons a actions ih =>
    cases ht : transition a s with
    | error e => simp [run, ht, Except.bind] at hs
    | ok mid =>
      have hrest : run transition actions mid = .ok s' := by simpa [run,ht,Except.bind] using hs
      iintro Hs
      iapply ownP_lift_step
      iapply fupd_mask_intro empty_subset
      iintro Hclose
      iexists s
      isplit
      · ipureintro
        exact ⟨[],Expr.script actions,mid,[],Prim.next ht⟩
      isplitl [Hs]
      · inext; iexact Hs
      · inext
        iintro %obs %e' %next %ef %hp Hnext
        change Prim transition (.script (a::actions),s) obs (e',next,ef) at hp
        cases hp with
        | next h =>
          have heq : mid = next := Except.ok.inj (ht.symm.trans h)
          subst next
          imod Hclose
          imodintro
          simp only [Iris.Algebra.BigOpL.bigOpL_nil]
          isplitl [Hnext]
          · iapply ih hrest $$ Hnext
          · itrivial
        | abort h => simp [ht] at h

theorem script_adequate {actions s s'} (hs : run transition actions s = .ok s') :
    adequate .NotStuck (Expr.script (transition := transition) actions) s (fun v _ => v = .ok s') := by
  apply ownP_adequacy (GF := GF State) .NotStuck (Expr.script actions) s (fun v => v = .ok s')
  intro _
  refine (script_wp hs).trans (wp_mono ?_)
  intro v
  iintro ⟨Hv, _⟩
  iexact Hv

/-- A successful local Hoare rule lifts to Iris without assuming the caller has
already exhibited the final state. All physical preconditions remain explicit. -/
theorem rule_wp [OwnPGS State (GF State)] (P Q : State → Prop) (a : Action)
    (rule : ∀ s, P s → ∃ s', transition a s = .ok s' ∧ Q s') :
    (∃ s, ⌜P s⌝ ∗ ownP (GF := GF State) s) ⊢
      WP (Expr.invoke (transition := transition) a)
        {{ v, ∃ s', ⌜v = .ok s' ∧ Q s'⌝ ∗ ownP s' }} := by
  iintro ⟨%s, %hp, Hs⟩
  obtain ⟨s',hs,hq⟩ := rule s hp
  ihave Hwp := invoke_wp hs $$ Hs
  iapply wp_mono (Φ := fun v => iprop(⌜v = .ok s'⌝ ∗ ownP (after s v))) ?_ $$ Hwp
  intro v
  iintro ⟨%hv, Hnext⟩
  subst v
  simp only [after]
  iexists s'
  isplit
  · ipureintro; exact ⟨rfl,hq⟩
  · iexact Hnext

theorem invoke_exec {s a r} (hs : transition a s = r) :
    ([Expr.invoke (transition := transition) a],s) -·->ₜₚ*
      ([Expr.result r],after s r) := by
  apply FromMathlib.Relation.ReflTransGen.single
  refine ⟨[], ?_⟩
  cases r with
  | ok s' => exact Step.of_primStep (t₁ := []) (t₂ := []) (Prim.success hs)
  | error e => exact Step.of_primStep (t₁ := []) (t₂ := []) (Prim.reject hs)

/-- A rejected script has a real error execution. It keeps the state of its
successful prefix; no rollback of earlier effects is silently inserted. -/
theorem script_reject_exec {actions s error} (hs : run transition actions s = .error error) :
    ∃ current, ([Expr.script (transition := transition) actions],s) -·->ₜₚ*
      ([Expr.result (.error error)],current) := by
  induction actions generalizing s with
  | nil => simp [run] at hs
  | cons a actions ih =>
    cases ht : transition a s with
    | error e =>
      have he : e = error := by simpa [run,ht,Except.bind] using hs
      subst e
      refine ⟨s,FromMathlib.Relation.ReflTransGen.single ⟨[],?_⟩⟩
      exact Step.of_primStep (t₁ := []) (t₂ := []) (Prim.abort ht)
    | ok mid =>
      have hrest : run transition actions mid = .error error := by simpa [run,ht,Except.bind] using hs
      obtain ⟨current,hreach⟩ := ih hrest
      refine ⟨current, FromMathlib.Relation.ReflTransGen.head ?_ hreach⟩
      exact ⟨[],Step.of_primStep (t₁ := []) (t₂ := []) (Prim.next ht)⟩

/-- NotStuck includes error returns. Exact success adequacy is impossible for an
actual rejected action, independently of how a proof is attempted. -/
theorem reject_not_ok_adequate {s a error} (hs : transition a s = .error error) :
    ¬ adequate .NotStuck (Expr.invoke (transition := transition) a) s
      (fun v _ => ∃ s', v = .ok s') := by
  intro ha
  obtain ⟨s',hv⟩ := ha.adequate_result [] s (.error error) (invoke_exec hs)
  cases hv

theorem script_reject_not_ok_adequate {actions s error}
    (hs : run transition actions s = .error error) :
    ¬ adequate .NotStuck (Expr.script (transition := transition) actions) s
      (fun v _ => ∃ s', v = .ok s') := by
  intro ha
  obtain ⟨current,hreach⟩ := script_reject_exec hs
  obtain ⟨s',hv⟩ := ha.adequate_result [] current (.error error) hreach
  cases hv

end Ptx.IrisExecution
