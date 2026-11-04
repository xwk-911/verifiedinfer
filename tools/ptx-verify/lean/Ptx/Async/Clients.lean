import Ptx.Async.Contracts

/-! Universal client contracts over all finite successful interleavings of the
issued async protocols. Phase machines are proof indices: their transitions are
checked equal to the REAL Async.step, not substituted as trusted semantics.
Data remains an arbitrary Nat. These are unbounded trace/invariant proofs, not
enumerations of execution schedules or concrete input values.
-/
namespace Ptx.Async.Client

inductive Steps (interpret : α → Action) : State → State → Prop where
  | refl (s) : Steps interpret s s
  | next {s mid final} (a : α) : step s (interpret a) = .ok mid →
      Steps interpret mid final → Steps interpret s final

theorem steps_sound {interpret : α → Action} {s final} (hs : Steps interpret s final) :
    Async.Steps s final := by
  induction hs with
  | refl => exact .refl _
  | next a hstep _ ih => exact .next _ hstep ih

theorem invariant_steps {interpret : α → Action} (I : State → Prop)
    (rule : ∀ {s next} (a : α), I s → step s (interpret a) = .ok next → I next)
    {s final} (hi : I s) (hs : Steps interpret s final) : I final := by
  induction hs with
  | refl => exact hi
  | next a hstep _ ih => exact ih (rule a hi hstep)

theorem run_steps {interpret : α → Action} {actions : List α} {s final}
    (hs : run s (actions.map interpret) = .ok final) : Steps interpret s final := by
  induction actions generalizing s with
  | nil => simp only [List.map_nil,run,Except.ok.injEq] at hs; subst final; exact .refl _
  | cons a actions ih =>
    cases hstep : step s (interpret a) with
    | error e => simp [List.map_cons,run,hstep,Except.bind] at hs
    | ok mid =>
      exact .next a hstep (ih (by simpa [List.map_cons,run,hstep,Except.bind] using hs))

theorem run_append (s : State) (first last : List Action) :
    run s (first ++ last) = (run s first).bind (fun mid => run mid last) := by
  induction first generalizing s with
  | nil => rfl
  | cons a first ih =>
    cases hstep : step s a <;> simp [run,hstep,Except.bind,ih]

def Drained (s : State) : Prop := s.streams.all (fun st => st.queue.isEmpty) = true
def Returned (s : State) : Prop := s.buffers.all (fun b => b.loans.isEmpty) = true

inductive PrefetchAction | producer | consumer | acquireProducer | acquireConsumer
def PrefetchAction.interpret : PrefetchAction → Action
  | .producer => .device 0
  | .consumer => .device 1
  | .acquireProducer => .acquire 7
  | .acquireConsumer => .acquire 8

structure PrefetchPhase where
  producer : Bool
  waited : Bool
  consumed : Bool
  acquiredProducer : Bool
  acquiredConsumer : Bool

def PrefetchPhase.Valid (p : PrefetchPhase) : Prop :=
  (p.waited = true → p.producer = true) ∧
  (p.consumed = true → p.waited = true) ∧
  (p.acquiredProducer = true → p.producer = true) ∧
  (p.acquiredConsumer = true → p.consumed = true)

def prefetchState (value : Nat) (p : PrefetchPhase) : State := {
  streams := [
    ⟨1,if p.producer then 1 else 0,if p.producer then [] else [.copy 0 1],[]⟩,
    ⟨2,if p.consumed then 2 else if p.waited then 1 else 0,
      if p.consumed then [] else if p.waited then [.use 1] else [.wait ⟨0,1⟩,.use 1], [⟨0,1⟩]⟩]
  buffers := [
    {value := value,loans := if p.acquiredProducer then [] else [⟨⟨0,1⟩,.read⟩]},
    {value := if p.producer then value else 0,
      loans := (if p.acquiredConsumer then [] else [⟨⟨1,2⟩,.read⟩]) ++
        (if p.acquiredProducer then [] else [⟨⟨0,1⟩,.write⟩])}]
  events := [⟨8,⟨1,2⟩⟩,⟨7,⟨0,1⟩⟩]
}

def prefetchPhaseStep (p : PrefetchPhase) : PrefetchAction → Except Error PrefetchPhase
  | .producer => if p.producer then .error .emptyQueue else .ok {p with producer := true}
  | .consumer => if p.consumed then .error .emptyQueue
      else if p.waited then .ok {p with consumed := true}
      else if p.producer then .ok {p with waited := true} else .error .notComplete
  | .acquireProducer => if p.producer then .ok {p with acquiredProducer := true} else .error .notComplete
  | .acquireConsumer => if p.consumed then .ok {p with acquiredConsumer := true} else .error .notComplete

/-- The proof-index transition is checked against the executable queue/loan
semantics, including empty queues, blocked waits and event errors. -/
theorem prefetch_transition (value : Nat) (p : PrefetchPhase) (a : PrefetchAction) :
    step (prefetchState value p) a.interpret =
      (prefetchPhaseStep p a).bind (fun next => .ok (prefetchState value next)) := by
  rcases p with ⟨pd,wd,ud,ap,ac⟩
  cases pd <;> cases wd <;> cases ud <;> cases ap <;> cases ac <;> cases a <;>
    with_unfolding_all rfl

theorem prefetch_phase_valid {p next a} (hp : PrefetchPhase.Valid p)
    (hs : prefetchPhaseStep p a = .ok next) : PrefetchPhase.Valid next := by
  rcases p with ⟨pd,wd,ud,ap,ac⟩
  cases pd <;> cases wd <;> cases ud <;> cases ap <;> cases ac <;> cases a <;>
    simp_all [PrefetchPhase.Valid,prefetchPhaseStep]
  all_goals subst next; simp

def PrefetchInv (value : Nat) (s : State) : Prop :=
  ∃ p, PrefetchPhase.Valid p ∧ s = prefetchState value p

theorem prefetch_initial (value : Nat) : PrefetchInv value (Contracts.prefetchIssued value) := by
  refine ⟨⟨false,false,false,false,false⟩,by simp [PrefetchPhase.Valid],?_⟩
  with_unfolding_all rfl

theorem prefetch_step {value s next} {a : PrefetchAction} (hi : PrefetchInv value s)
    (hs : step s a.interpret = .ok next) : PrefetchInv value next := by
  obtain ⟨p,hp,rfl⟩ := hi
  rw [prefetch_transition] at hs
  cases hphase : prefetchPhaseStep p a with
  | error e => simp [hphase,Except.bind] at hs
  | ok phase =>
    simp only [hphase,Except.bind] at hs
    cases Except.ok.inj hs
    exact ⟨phase,prefetch_phase_valid hp hphase,rfl⟩

theorem prefetch_invariant {value final}
    (hs : Steps PrefetchAction.interpret (Contracts.prefetchIssued value) final) : PrefetchInv value final := by
  exact invariant_steps (PrefetchInv value) (fun _ hi hstep => prefetch_step hi hstep)
    (prefetch_initial value) hs

theorem prefetch_finished {value final}
    (hs : Steps PrefetchAction.interpret (Contracts.prefetchIssued value) final)
    (hd : Drained final) (hr : Returned final) : final = Contracts.prefetchFinal value := by
  obtain ⟨p,hp,rfl⟩ := prefetch_invariant hs
  rcases p with ⟨pd,wd,ud,ap,ac⟩
  cases pd <;> cases wd <;> cases ud <;> cases ap <;> cases ac <;>
    simp_all [PrefetchPhase.Valid,Drained,Returned,prefetchState,Contracts.prefetchFinal]

/-- Once the consumer's queued wait has executed, its input is already the exact
producer value, even before the consumer or either host acquire has finished. -/
theorem prefetch_consumer_value {value final}
    (hs : Steps PrefetchAction.interpret (Contracts.prefetchIssued value) final)
    (hw : ∃ st, final.streams[1]? = some st ∧ 0 < st.completed) :
    (final.buffers[1]?).map Buffer.value = some value := by
  obtain ⟨p,hp,rfl⟩ := prefetch_invariant hs
  obtain ⟨st,hst,hcompleted⟩ := hw
  rcases p with ⟨pd,wd,ud,ap,ac⟩
  cases pd <;> cases wd <;> cases ud <;> cases ap <;> cases ac <;>
    simp_all [PrefetchPhase.Valid,prefetchState]
  all_goals subst st; simp at hcompleted

inductive DeferredAction | device | acquire | reclaim
def DeferredAction.interpret : DeferredAction → Action
  | .device => .device 0
  | .acquire => .acquire 9
  | .reclaim => .reclaim 0

structure DeferredPhase where
  completed : Bool
  acquired : Bool
  reclaimed : Bool

def DeferredPhase.Valid (p : DeferredPhase) : Prop :=
  (p.acquired = true → p.completed = true) ∧ (p.reclaimed = true → p.acquired = true)

def deferredState (value : Nat) (p : DeferredPhase) : State := {
  streams := [⟨1,if p.completed then 1 else 0,if p.completed then [] else [.use 0],[]⟩]
  buffers := [{value := value,alive := Bool.not p.reclaimed,loans := if p.acquired then [] else [⟨⟨0,1⟩,.read⟩]}]
  events := [⟨9,⟨0,1⟩⟩]
}

def deferredPhaseStep (p : DeferredPhase) : DeferredAction → Except Error DeferredPhase
  | .device => if p.completed then .error .emptyQueue else if p.reclaimed then .error .freed
      else .ok {p with completed := true}
  | .acquire => if p.completed then .ok {p with acquired := true} else .error .notComplete
  | .reclaim => if p.reclaimed then .error .freed else if p.acquired then .ok {p with reclaimed := true}
      else .error .outstandingLoan

theorem deferred_transition (value : Nat) (p : DeferredPhase) (a : DeferredAction) :
    step (deferredState value p) a.interpret =
      (deferredPhaseStep p a).bind (fun next => .ok (deferredState value next)) := by
  rcases p with ⟨done,acquired,reclaimed⟩
  cases done <;> cases acquired <;> cases reclaimed <;> cases a <;>
    with_unfolding_all rfl

theorem deferred_phase_valid {p next a} (hp : DeferredPhase.Valid p)
    (hs : deferredPhaseStep p a = .ok next) : DeferredPhase.Valid next := by
  rcases p with ⟨done,acquired,reclaimed⟩
  cases done <;> cases acquired <;> cases reclaimed <;> cases a <;>
    simp_all [DeferredPhase.Valid,deferredPhaseStep]
  all_goals subst next; simp

def DeferredInv (value : Nat) (s : State) : Prop :=
  ∃ p, DeferredPhase.Valid p ∧ s = deferredState value p

theorem deferred_initial (value : Nat) : DeferredInv value (Contracts.deferredIssued value) := by
  refine ⟨⟨false,false,false⟩,by simp [DeferredPhase.Valid],?_⟩
  with_unfolding_all rfl

theorem deferred_step {value s next} {a : DeferredAction} (hi : DeferredInv value s)
    (hs : step s a.interpret = .ok next) : DeferredInv value next := by
  obtain ⟨p,hp,rfl⟩ := hi
  rw [deferred_transition] at hs
  cases hphase : deferredPhaseStep p a with
  | error e => simp [hphase,Except.bind] at hs
  | ok phase =>
    simp only [hphase,Except.bind] at hs
    cases Except.ok.inj hs
    exact ⟨phase,deferred_phase_valid hp hphase,rfl⟩

theorem deferred_invariant {value final}
    (hs : Steps DeferredAction.interpret (Contracts.deferredIssued value) final) : DeferredInv value final := by
  exact invariant_steps (DeferredInv value) (fun _ hi hstep => deferred_step hi hstep)
    (deferred_initial value) hs

/-- Reclamation implies actual device completion and event acquisition in every
successful client schedule. No fairness or eventual reclamation is assumed. -/
theorem deferred_finished {value final}
    (hs : Steps DeferredAction.interpret (Contracts.deferredIssued value) final)
    (hf : final.buffers.all (fun b => !b.alive) = true) : final = Contracts.deferredFinal value := by
  obtain ⟨p,hp,rfl⟩ := deferred_invariant hs
  rcases p with ⟨done,acquired,reclaimed⟩
  cases done <;> cases acquired <;> cases reclaimed <;>
    simp_all [DeferredPhase.Valid,deferredState,Contracts.deferredFinal]

/-- A second actual ordering acquires the producer before running the consumer.
This executable witness complements the universal invariant above. -/
theorem prefetch_alternate (value : Nat) :
    run (initial 2 [value,0]) (Contracts.prefetchPrefix ++
      [.device 0,.acquire 7,.device 1,.device 1,.acquire 8]) = .ok (Contracts.prefetchFinal value) := by rfl

end Ptx.Async.Client
