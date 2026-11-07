import Ptx.Hopper.Mbarrier

/-! Conservation laws for arbitrary admitted mbarrier histories. Accounting is
reset at every initialization, so reinitialized objects cannot inherit earlier
arrivals or transaction credits. These equations follow from the operational
semantics; they do not grant publication or attribute a wait to a copy. -/
namespace Ptx.Hopper.Mbarrier
open Ptx.ISA

structure Accounting where
  expected : Nat := 0
  arrivals : Nat := 0
  added : Nat := 0
  completed : Nat := 0
  deriving Repr, DecidableEq

def accountStep (a : Accounting) : BarrierOp → Accounting
  | .init n => ⟨n,0,0,0⟩
  | .arriveExpectTx n => {a with arrivals := a.arrivals+1,added := a.added+n}
  | .completeTx n => {a with completed := a.completed+n}
  | _ => a

def account (ops : List BarrierOp) : Accounting := ops.foldl accountStep {}
def arrivalPotential (s : PhaseState) : Nat := s.phase*s.expected+(s.expected-s.pending)
def Accounting.Agrees (a : Accounting) : Object → Prop
  | none => True
  | some s => s.expected = a.expected ∧ s.tx = (a.added : Int)-(a.completed : Int) ∧
      arrivalPotential s = a.arrivals

theorem finish_expected (s : PhaseState) : (finish s).expected = s.expected := by
  unfold finish
  split <;> rfl

theorem finish_transactions (s : PhaseState) : (finish s).tx = s.tx := by
  unfold finish
  split <;> rfl

theorem finish_arrival_potential (s : PhaseState) : arrivalPotential (finish s) = arrivalPotential s := by
  unfold finish
  split
  · rename_i h
    simp [arrivalPotential,h.1,Nat.add_mul]
  · rfl

theorem accept_accounting {s next} {a : Accounting} (ha : a.Agrees (some s)) (h : accept s = some next) : a.Agrees next := by
  unfold accept at h
  split at h
  · cases h
    simpa only [Accounting.Agrees,finish_expected,finish_transactions,finish_arrival_potential] using ha
  · cases h

theorem step_accounting {s next a op} (hw : ObjectWellFormed s) (ha : a.Agrees s)
    (h : step s op = some next) : (accountStep a op).Agrees next := by
  cases s with
  | none =>
    cases op <;> simp only [step] at h <;> try cases h
    split at h
    · cases h
      simp [accountStep,Accounting.Agrees,initialized,arrivalPotential]
    · cases h
  | some s =>
    rcases ha with ⟨he,ht,hp⟩
    cases op with
    | init n => cases h
    | inval => cases h; trivial
    | arriveExpectTx n =>
      simp only [step] at h
      split at h
      · rename_i hg
        apply accept_accounting (a := accountStep a (.arriveExpectTx n)) ?_ h
        refine ⟨he,?_,?_⟩
        · simp only [accountStep,Nat.cast_add]
          omega
        · have hbound := hw.2.2.1
          have hpositive := hg.2.1
          dsimp only [arrivalPotential,accountStep] at hp ⊢
          omega
      · cases h
    | completeTx n =>
      simp only [step] at h
      split at h
      · apply accept_accounting (a := accountStep a (.completeTx n)) ?_ h
        refine ⟨he,?_,hp⟩
        simp only [accountStep,Nat.cast_add]
        omega
      · cases h
    | tryWaitParity p complete =>
      simp only [step] at h
      split at h
      · split at h
        · cases h
          exact ⟨he,ht,hp⟩
        · cases h
      · cases h
        exact ⟨he,ht,hp⟩

theorem run_accounting_from {s next a ops} (hw : ObjectWellFormed s) (ha : a.Agrees s)
    (h : run s ops = some next) : (ops.foldl accountStep a).Agrees next := by
  induction ops generalizing s a with
  | nil => cases h; exact ha
  | cons op ops ih =>
    cases hs : step s op with
    | none => simp [run,hs] at h
    | some mid =>
      have hr : run mid ops = some next := by simpa only [run,hs,Option.bind_some] using h
      exact ih (step_wf hw hs) (step_accounting hw ha hs) hr

theorem run_accounting {ops next} (h : run none ops = some next) : (account ops).Agrees next :=
  run_accounting_from (s := none) trivial trivial h

theorem run_take_accounting {ops next} (h : run none ops = some next) (cut : Nat) :
    ∃ before, run none (ops.take cut) = some before ∧ ObjectWellFormed before ∧ (account (ops.take cut)).Agrees before := by
  have hr : (run none (ops.take cut)).bind (fun mid => run mid (ops.drop cut)) = some next := by
    rw [← run_append,List.take_append_drop]
    exact h
  cases hs : run none (ops.take cut) with
  | none => simp [hs] at hr
  | some before => exact ⟨before,rfl,run_wf (s := none) trivial hs,run_accounting hs⟩

def UnitInitialization : BarrierOp → Prop
  | .init n => n = 1
  | _ => True

theorem account_step_expected_le_one {a : Accounting} {op} (ha : a.expected ≤ 1) (hu : UnitInitialization op) :
    (accountStep a op).expected ≤ 1 := by
  cases op <;> simp_all [UnitInitialization,accountStep]

theorem account_expected_le_one_from {ops : List BarrierOp} {a : Accounting} (ha : a.expected ≤ 1)
    (hu : ∀ op ∈ ops, UnitInitialization op) : (ops.foldl accountStep a).expected ≤ 1 := by
  induction ops generalizing a with
  | nil => exact ha
  | cons op rest ih =>
    exact ih (account_step_expected_le_one ha (hu op (by simp))) (fun x hx => hu x (by simp [hx]))

theorem account_expected_le_one {ops} (hu : ∀ op ∈ ops, UnitInitialization op) : (account ops).expected ≤ 1 :=
  account_expected_le_one_from (by decide) hu

theorem run_unit_accounting {ops state} (hu : ∀ op ∈ ops, UnitInitialization op)
    (h : run none ops = some (some state)) :
    state.expected = 1 ∧ state.pending ≤ 1 ∧
      state.phase+1 = (account ops).arrivals+state.pending ∧
      state.tx = ((account ops).added : Int)-((account ops).completed : Int) := by
  have hw := run_wf (s := none) trivial h
  obtain ⟨he,ht,hp⟩ := run_accounting h
  have hb := account_expected_le_one hu
  have hpositive : 0 < state.expected := hw.1
  have hone : state.expected = 1 := by omega
  refine ⟨hone,?_,?_,ht⟩
  · have := hw.2.2.1
    omega
  · dsimp only [arrivalPotential] at hp
    rw [hone,Nat.mul_one] at hp
    have := hw.2.2.1
    omega

theorem account_append (first rest : List BarrierOp) :
    account (first++rest) = rest.foldl accountStep (account first) := by
  simp only [account,List.foldl_append]

theorem account_reinitialization (first rest : List BarrierOp) (n : Nat) :
    account (first++ .init n :: rest) = rest.foldl accountStep ⟨n,0,0,0⟩ := by
  rw [account_append]
  rfl

end Ptx.Hopper.Mbarrier
