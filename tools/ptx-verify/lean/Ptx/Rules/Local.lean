import Ptx.Contracts

/-! Lifting thread-local contracts to arbitrarily scheduled CTA executions.
These rules use the interpreter's localStep; they do not introduce another meaning
for integer/control instructions. Memory instructions require separate rules. -/
namespace Ptx

@[simp] theorem lookup_put_same (r : String) (v : Nat) (xs : Bindings) :
    lookup r (put r v xs) = some v := by simp [lookup, put]

theorem lookup_filter_other {r k : String} (hne : r ≠ k) (xs : Bindings) :
    lookup r (xs.filter (fun kv => kv.1 != k)) = lookup r xs := by
  induction xs with
  | nil => rfl
  | cons kv xs ih =>
    rcases kv with ⟨name,v⟩
    by_cases hk : name = k
    · subst name
      simp [lookup, Ne.symm hne, ih]
    · by_cases hr : name = r
      · subst name; simp [lookup, hk]
      · simp [lookup, hk, hr, ih]

@[simp] theorem lookup_put_other {r k : String} (hne : r ≠ k) (v : Nat) (xs : Bindings) :
    lookup r (put k v xs) = lookup r xs := by
  simp [put, lookup, Ne.symm hne, lookup_filter_other hne]

theorem threadStep_local {code tid m t i}
    (ht : m.threads[tid]? = some t) (hs : t.status = .running)
    (hp : code[t.pc]? = some i) (hl : isLocal i = true) :
    threadStep code tid m = (localStep m.params tid t i).map (updateThread m tid) := by
  cases i <;> simp_all [isLocal, threadStep, bind, Except.bind, pure, Except.pure,
    Except.map]

/-- Every CTA thread satisfies its own local invariant. No launch-size bound. -/
def AllThreads (I : Thread → Prop) (m : Machine) : Prop := ∀ t ∈ m.threads, I t

/-- A local proof must show successful execution and preservation, not merely
postconditions conditional on success. Barrier-free kernels cannot create waits. -/
def LocalInvariant (code : List Instr) (I : Thread → Prop) : Prop :=
  (∀ t, I t → t.status = .running ∨ t.status = .done) ∧
  ∀ params tid t, I t → t.status = .running →
    ∃ i t', code[t.pc]? = some i ∧ isLocal i = true ∧
      localStep params tid t i = .ok t' ∧ I t'

theorem allThreads_update {I m tid t'} (hi : AllThreads I m) (ht' : I t') :
    AllThreads I (updateThread m tid t') := by
  intro t ht
  have : t ∈ m.threads ∨ t = t' := List.mem_or_eq_of_mem_set ht
  rcases this with h | h
  · exact hi _ h
  · subst t; exact ht'

theorem localInvariant_transition {code I m m' a} (hi : LocalInvariant code I)
    (hall : AllThreads I m) (hs : step code a m = .ok m') :
    ∃ tid t i t', m.threads[tid]? = some t ∧ t.status = .running ∧
      code[t.pc]? = some i ∧ isLocal i = true ∧
      localStep m.params tid t i = .ok t' ∧ m' = updateThread m tid t' ∧ I t' := by
  cases a with
  | thread tid =>
    cases ht : m.threads[tid]? with
    | none => simp [step, threadStep, ht, bind, Except.bind] at hs
    | some t =>
      have hit := hall t (List.mem_of_getElem? ht)
      rcases hi.1 t hit with hr | hd
      · obtain ⟨i,t',hp,hl,hstep,hit'⟩ := hi.2 m.params tid t hit hr
        rw [step, threadStep_local ht hr hp hl, hstep] at hs
        have heq : updateThread m tid t' = m' := by simpa [Except.map] using hs
        exact ⟨tid,t,i,t',ht,hr,hp,hl,hstep,heq.symm,hit'⟩
      · simp [step, threadStep, ht, hd, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs
  | release =>
    cases ht : m.threads.head? with
    | none => simp [step, release, ht, bind, Except.bind] at hs
    | some t =>
      have hit := hall t (List.mem_of_head? ht)
      rcases hi.1 t hit with hr | hd
      · simp [step, release, ht, hr, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs
      · simp [step, release, ht, hd, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs

theorem localInvariant_inductive {code I} (hi : LocalInvariant code I) :
    InductiveInvariant code (AllThreads I) := by
  intro m a m' hall hs
  obtain ⟨tid,_,_,t',_,_,_,_,_,heq,hi'⟩ := localInvariant_transition hi hall hs
  rw [heq]
  exact allThreads_update hall hi'

theorem localInvariant_safe {code I} (hi : LocalInvariant code I) :
    Safe code (AllThreads I) := by
  intro m m' hp hs tid t ht hr
  have hall := invariant_steps (localInvariant_inductive hi) hs hp
  have hit := hall t (List.mem_of_getElem? ht)
  obtain ⟨i,t',hpc,hl,hlocal,_⟩ := hi.2 m'.params tid t hit hr
  exact ⟨updateThread m' tid t', by rw [threadStep_local ht hr hpc hl, hlocal]; rfl⟩

/-- No barrier-deadlock can hide in a barrier-free local invariant: a nonfinished
CTA has a concrete runnable thread with a successful next step. This is a progress
claim for the modeled state, not fairness or a host scheduling guarantee. -/
theorem localInvariant_progress {code I m} (hi : LocalInvariant code I)
    (hall : AllThreads I m) (hnot : m.threads.all (fun t => t.status == .done) ≠ true) :
    ∃ tid next, threadStep code tid m = .ok next := by
  have hf : m.threads.all (fun t => t.status == .done) = false := by
    cases h : m.threads.all (fun t => t.status == .done)
    · rfl
    · exact (hnot h).elim
  obtain ⟨t,ht,hnd⟩ := List.all_eq_false.mp hf
  have hnd : t.status ≠ .done := by simpa using hnd
  obtain ⟨tid,htid⟩ := List.mem_iff_getElem?.mp ht
  have hit := hall t ht
  have hr : t.status = .running := (hi.1 t hit).resolve_right hnd
  obtain ⟨i,t',hpc,hl,hstep,_⟩ := hi.2 m.params tid t hit hr
  exact ⟨tid,_, by rw [threadStep_local htid hr hpc hl, hstep]; rfl⟩

/-- A local instruction preserves all physical memory and non-thread state.
This property is proved for arbitrary finite executions, not a selected schedule. -/
def SameEnvironment (m m' : Machine) : Prop :=
  m'.globalMem = m.globalMem ∧ m'.sharedMem = m.sharedMem ∧
  m'.params = m.params ∧ m'.epoch = m.epoch ∧ m'.history = m.history ∧
  m'.threads.length = m.threads.length

theorem localInvariant_frame {code I m m'} (hi : LocalInvariant code I)
    (hall : AllThreads I m) (hs : Steps code m m') : SameEnvironment m m' := by
  induction hs with
  | refl => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  | next a hs hrest ih =>
    obtain ⟨tid,_,_,t',_,_,_,_,_,heq,_⟩ := localInvariant_transition hi hall hs
    have henv := ih (localInvariant_inductive hi _ a _ hall hs)
    simpa [heq, SameEnvironment, updateThread] using henv

end Ptx
