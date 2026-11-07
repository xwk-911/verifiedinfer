import Ptx.Rules.Memory
import Lean.Elab.Tactic.Omega

/-! Finite completion from a checked decreasing potential and concrete progress.
This constructs an execution of the fixed interpreter; it does not assume
scheduler fairness or turn partial correctness into a runtime guarantee.
-/
namespace Ptx.Termination

def threadWork (limit : Nat) (t : Thread) : Nat :=
  if t.status = .done then 0 else limit-t.pc

def ForwardAt (pc : Nat) : Instr → Prop
  | .branch _ _ target | .jump target => pc < target
  | _ => True

instance (pc : Nat) (i : Instr) : Decidable (ForwardAt pc i) := by
  cases i <;> simp only [ForwardAt] <;> infer_instance

theorem local_work_decreases {limit params tid t i t'}
    (hr : t.status = .running) (hb : t.pc < limit) (hf : ForwardAt t.pc i)
    (hs : localStep params tid t i = .ok t') :
    threadWork limit t' < threadWork limit t := by
  cases i <;>
    simp only [localStep,bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at hs
  all_goals
    repeat' first | split at hs | (cases hs)
    all_goals simp_all [threadWork,assign,advance,ForwardAt]
    all_goals omega

theorem checkedAccess_threads {m a m'} (hs : checkedAccess m a = .ok m') :
    m'.threads = m.threads := by
  unfold checkedAccess at hs
  split at hs <;> try cases hs
  split at hs <;> try cases hs
  split at hs <;> cases hs
  rfl

theorem setMemory_threads (m : Machine) (space : Space) (cells : List (Option Nat)) :
    (setMemory m space cells).threads = m.threads := by cases space <;> rfl

/-- Successful interpreter steps change one thread. Memory steps advance its PC;
other steps use the existing local semantics. Heap/race checks are still executed
by the interpreter and are not replaced by this projection. -/
theorem threadStep_shape {code tid m m' t}
    (ht : m.threads[tid]? = some t) (hr : t.status = .running)
    (hs : threadStep code tid m = .ok m') :
    ∃ i t', code[t.pc]? = some i ∧ m'.threads = m.threads.set tid t' ∧
      ((isLocal i = true ∧ localStep m.params tid t i = .ok t') ∨
        (t'.pc = t.pc+1 ∧ t'.status = t.status)) := by
  cases hc : code[t.pc]? with
  | none => simp [threadStep,ht,hr,hc,bind,Except.bind] at hs
  | some i =>
    by_cases hl : isLocal i = true
    · rw [threadStep_local ht hr hc hl] at hs
      cases he : localStep m.params tid t i with
      | error e => simp [he,Except.map] at hs
      | ok t' =>
        have hm : updateThread m tid t' = m' := by simpa [he,Except.map] using hs
        exact ⟨i,t',rfl,by rw [← hm]; rfl,Or.inl ⟨hl,he⟩⟩
    · cases i with
      | load space dst address =>
        simp [threadStep,ht,hr,hc,bind,Except.bind,pure,Except.pure] at hs
        repeat' first | split at hs | (cases hs)
        rename_i _ _ _ _ mid hcheck _ value _
        have hf := checkedAccess_threads hcheck
        exact ⟨_,assign t dst (wrap 32 value),rfl,by simp only [updateThread,hf],Or.inr ⟨rfl,rfl⟩⟩
      | store space address operand =>
        simp [threadStep,ht,hr,hc,bind,Except.bind,pure,Except.pure] at hs
        repeat' first | split at hs | (cases hs)
        rename_i _ _ _ _ _ _ _ mid hcheck
        have hf := checkedAccess_threads hcheck
        exact ⟨_,advance t,rfl,by simp only [updateThread,setMemory_threads,hf],Or.inr ⟨rfl,rfl⟩⟩
      | _ => simp [isLocal] at hl

def potential (rank : Thread → Nat) : List Thread → Nat
  | [] => 0
  | t::ts => rank t + potential rank ts

theorem potential_map_eq {rank : Thread → Nat} {f : Thread → Thread} {ts : List Thread}
    (he : ∀ t ∈ ts, rank (f t) = rank t) : potential rank (ts.map f) = potential rank ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons,potential,he t (by simp)]
    rw [ih (fun u hu => he u (by simp [hu]))]

theorem potential_set_lt {rank : Thread → Nat} {ts : List Thread} {tid : Nat} {t t' : Thread}
    (ht : ts[tid]? = some t) (hdrop : rank t' < rank t) :
    potential rank (ts.set tid t') < potential rank ts := by
  induction ts generalizing tid with
  | nil => simp at ht
  | cons head tail ih =>
    cases tid with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at ht; subst t
              simpa only [List.set_cons_zero,potential] using Nat.add_lt_add_right hdrop (potential rank tail)
    | succ tid =>
      have ht' : tail[tid]? = some t := by simpa only [List.getElem?_cons_succ] using ht
      simpa only [List.set_cons_succ,potential] using Nat.add_lt_add_left (ih ht') (rank head)

theorem completed_execution {code : List Instr} {I : Assertion} (rank : Machine → Nat)
    (hinv : InductiveInvariant code I)
    (hprogress : ∀ m, I m → m.threads.all (fun t => t.status == .done) ≠ true →
      ∃ action next, step code action m = .ok next ∧ rank next < rank m)
    {m : Machine} (hi : I m) :
    ∃ m', Steps code m m' ∧ m'.threads.all (fun t => t.status == .done) = true := by
  have hall : ∀ fuel m, rank m = fuel → I m →
      ∃ m', Steps code m m' ∧ m'.threads.all (fun t => t.status == .done) = true := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro m he hi
      by_cases hd : m.threads.all (fun t => t.status == .done) = true
      · exact ⟨m,.refl m,hd⟩
      · obtain ⟨action,next,hs,hlt⟩ := hprogress m hi hd
        obtain ⟨last,hsteps,hdone⟩ := ih (rank next) (by omega) next rfl (hinv m action next hi hs)
        exact ⟨last,.next action hs hsteps,hdone⟩
  exact hall (rank m) m rfl hi

/-- Relational witnesses can be replayed by the executable interpreter, including
the empty schedule. This is the converse of the baseline's `run_sound`. -/
theorem steps_run {code m m'} (hs : Steps code m m') :
    ∃ actions, run code actions m = .ok m' := by
  induction hs with
  | refl => exact ⟨[],rfl⟩
  | next action hstep _ ih =>
    obtain ⟨actions,hr⟩ := ih
    exact ⟨action::actions,by simp only [run,hstep,Except.bind]; exact hr⟩

end Ptx.Termination
