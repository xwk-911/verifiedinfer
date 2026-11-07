import Ptx.Hopper.Thread
import Mathlib.Data.Int.Basic

/-! A resource-local layout-v0 mbarrier protocol, separate from source execution.
Transaction counts are signed; arrival and transaction completion are distinct.
False try-waits are deliberately overapproximated even after completion. This
module does not yet establish cross-proxy visibility or global TMA matching. -/
namespace Ptx.Hopper.Mbarrier
open Ptx.ISA

def limit : Nat := 2^20-1
structure PhaseState where
  phase : Nat
  expected : Nat
  pending : Nat
  tx : Int
  observed : Bool
  deriving Repr, DecidableEq

def WellFormed (s : PhaseState) : Prop :=
  0 < s.expected ∧ s.expected ≤ limit ∧ s.pending ≤ s.expected ∧ -(limit : Int) ≤ s.tx ∧ s.tx ≤ (limit : Int)
instance (s) : Decidable (WellFormed s) := by unfold WellFormed; infer_instance
abbrev Object := Option PhaseState
def ObjectWellFormed : Object → Prop | none => True | some s => WellFormed s

def initialized (n : Nat) : PhaseState := ⟨0,n,n,0,true⟩
def finish (s : PhaseState) : PhaseState :=
  if s.pending = 0 ∧ s.tx = 0 then {s with phase := s.phase+1,pending := s.expected,observed := false} else s

def accept (s : PhaseState) : Option Object :=
  if WellFormed s then some (some (finish s)) else none

/-- The `some none` result invalidates an object. `none` rejects a protocol
history. This is an explicit resource-history interpretation, not an execution
scheduler and not a claim of ISA-level UB freedom. -/
def step : Object → BarrierOp → Option Object
  | none,.init n => if 0 < n ∧ n ≤ limit then some (some (initialized n)) else none
  | some _,.init _ => none
  | none,_ => none
  | some _,.inval => some none
  | some s,.arriveExpectTx n =>
      if s.observed = true ∧ 0 < s.pending ∧ n < 2^32 then
        accept {s with pending := s.pending-1,tx := s.tx+(n : Int)} else none
  | some s,.completeTx n => if n < 2^32 then accept {s with tx := s.tx-(n : Int)} else none
  | some s,.tryWaitParity p complete =>
      if complete then
        if 0 < s.phase ∧ p%2 ≠ s.phase%2 then some (some {s with observed := true}) else none
      else some (some s)

def run : Object → List BarrierOp → Option Object
  | s,[] => some s
  | s,op::rest => (step s op).bind (fun next => run next rest)
def Admitted (ops : List BarrierOp) : Prop := ∃ last, run none ops = some last

noncomputable def operationsAt (loc : Location) (events : List Hopper.Event) : List BarrierOp :=
  events.filterMap (fun event => match event with
    | .barrier e => if e.location = loc then some e.operation else none
    | _ => none)
noncomputable def AdmittedAt (loc : Location) (events : List Hopper.Event) : Prop := Admitted (operationsAt loc events)

theorem operationsAt_append (loc : Location) (first rest : List Hopper.Event) :
    operationsAt loc (first++rest) = operationsAt loc first ++ operationsAt loc rest := by
  simp [operationsAt,List.filterMap_append]

theorem run_append (s : Object) (first rest : List BarrierOp) :
    run s (first++rest) = (run s first).bind (fun mid => run mid rest) := by
  induction first generalizing s with
  | nil => rfl
  | cons op first ih =>
    simp only [List.cons_append,run]
    cases he : step s op <;> simp [he,ih]

theorem initialized_wf {n : Nat} (hn : 0 < n ∧ n ≤ limit) : WellFormed (initialized n) := by
  simp only [WellFormed,initialized]
  exact ⟨hn.1,hn.2,by omega,by norm_num [limit],by norm_num [limit]⟩
theorem finish_wf {s} (hs : WellFormed s) : WellFormed (finish s) := by
  unfold finish
  split
  · exact ⟨hs.1,hs.2.1,le_refl _,hs.2.2.2.1,hs.2.2.2.2⟩
  · exact hs

theorem finish_phase (s : PhaseState) : (finish s).phase =
    if s.pending = 0 ∧ s.tx = 0 then s.phase+1 else s.phase := by unfold finish; split <;> rfl
theorem finish_observed (s : PhaseState) : (finish s).observed =
    if s.pending = 0 ∧ s.tx = 0 then false else s.observed := by unfold finish; split <;> rfl

theorem incomplete_unchanged {s : PhaseState} (hs : s.pending ≠ 0 ∨ s.tx ≠ 0) : finish s = s := by
  simp only [finish]
  split
  · rename_i h
    rcases hs with hp | ht
    · exact (hp h.1).elim
    · exact (ht h.2).elim
  · rfl

theorem finish_advances_iff (s : PhaseState) : s.phase < (finish s).phase ↔ s.pending = 0 ∧ s.tx = 0 := by
  rw [finish_phase]
  split <;> simp_all

theorem accept_wf {s next} (h : accept s = some next) : ObjectWellFormed next := by
  unfold accept at h
  split at h
  · cases h
    exact finish_wf (by assumption)
  · cases h

theorem step_wf {s op next} (hs : ObjectWellFormed s) (h : step s op = some next) : ObjectWellFormed next := by
  cases s with
  | none =>
    cases op <;> simp only [step] at h <;> try cases h
    split at h
    · cases h
      exact initialized_wf (by assumption)
    · cases h
  | some s =>
    cases op with
    | init n => cases h
    | inval => cases h; trivial
    | arriveExpectTx n =>
      simp only [step] at h
      split at h
      · exact accept_wf h
      · cases h
    | completeTx n =>
      simp only [step] at h
      split at h
      · exact accept_wf h
      · cases h
    | tryWaitParity p complete =>
      simp only [step] at h
      split at h
      · split at h
        · cases h
          exact hs
        · cases h
      · cases h
        exact hs

theorem run_wf {s ops next} (hs : ObjectWellFormed s) (h : run s ops = some next) : ObjectWellFormed next := by
  induction ops generalizing s with
  | nil => cases h; exact hs
  | cons op rest ih =>
    simp only [run] at h
    cases he : step s op with
    | none => simp [he] at h
    | some mid =>
      simp only [he,Option.bind_some] at h
      exact ih (step_wf hs he) h

theorem arrive_requires_observation {s : PhaseState} {n next}
    (h : step (some s) (.arriveExpectTx n) = some next) : s.observed = true ∧ 0 < s.pending := by
  simp only [step] at h
  split at h
  · rename_i hh
    exact ⟨hh.1,hh.2.1⟩
  · cases h

theorem successful_wait_completed {s : PhaseState} {p next}
    (h : step (some s) (.tryWaitParity p true) = some next) :
    0 < s.phase ∧ p%2 ≠ s.phase%2 ∧ next = some {s with observed := true} := by
  simp only [step,ite_true] at h
  split at h
  · rename_i hh
    exact ⟨hh.1,hh.2,Option.some.inj h.symm⟩
  · cases h

theorem failed_wait_unchanged (s : PhaseState) (p : Nat) :
    step (some s) (.tryWaitParity p false) = some (some s) := by simp [step]

theorem next_arrive_without_wait_rejected {s : PhaseState} (hs : s.observed = false) (n : Nat) :
    step (some s) (.arriveExpectTx n) = none := by simp [step,hs]

theorem successful_wait_never_current {s : PhaseState} {p next}
    (hp : p%2 = s.phase%2) : step (some s) (.tryWaitParity p true) ≠ some next := by
  intro h
  exact (successful_wait_completed h).2.1 hp

/-- Reusable one-arriver transaction phase; its notification units are opaque
here. Matching a count to actual TMA bytes is a separate graph obligation. -/
theorem phase_cycle (phase count : Nat) (hn : 0 < count) (hb : count ≤ limit) :
    run (some ⟨phase,1,1,0,true⟩) [.arriveExpectTx count,.completeTx count,.tryWaitParity (phase%2) true] =
      some (some ⟨phase+1,1,1,0,true⟩) := by
  have hne : (count : Int) ≠ 0 := by omega
  have hpar : phase%2 ≠ (phase+1)%2 := by omega
  have hcn : count ≠ 0 := by omega
  have hwidth : count < 4294967296 := by
    have hl : limit < 4294967296 := by decide
    omega
  have hpositive : WellFormed ⟨phase,1,0,(count : Int),true⟩ := by
    change 0 < 1 ∧ 1 ≤ limit ∧ 0 ≤ 1 ∧ -(limit : Int) ≤ (count : Int) ∧ (count : Int) ≤ (limit : Int)
    refine ⟨by decide,by decide,by decide,?_,?_⟩
    · have hh := Int.natCast_nonneg count
      have hl : (0 : Int) ≤ (limit : Int) := by decide
      omega
    · exact_mod_cast hb
  have hzero : WellFormed ⟨phase,1,0,0,true⟩ := by norm_num [WellFormed,limit]
  simp [run,step,accept,finish,hwidth,hcn,hne,hpar,hpositive,hzero]

theorem two_phase_cycles (phase a b : Nat) (ha : 0 < a) (hab : a ≤ limit) (hb : 0 < b) (hbb : b ≤ limit) :
    run (some ⟨phase,1,1,0,true⟩)
      ([.arriveExpectTx a,.completeTx a,.tryWaitParity (phase%2) true]++
       [.arriveExpectTx b,.completeTx b,.tryWaitParity ((phase+1)%2) true]) =
      some (some ⟨phase+2,1,1,0,true⟩) := by
  rw [run_append,phase_cycle phase a ha hab]
  exact phase_cycle (phase+1) b hb hbb

end Ptx.Hopper.Mbarrier
