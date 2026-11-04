import Ptx.Async.Model

/-! Reachable-state lifetime invariant for the actual FIFO stream protocol.
Every queued memory access owns a live buffer loan at its exact sequence number.
This is not yet an ordering/functional or Iris global-adequacy theorem.
-/
namespace Ptx.Async

theorem getBuffer_iff {s bid b} : getBuffer s bid = .ok b ↔
    s.buffers[bid]? = some b ∧ b.alive = true := by
  unfold getBuffer
  cases hb : s.buffers[bid]? with
  | none => simp [bind,Except.bind]
  | some old =>
    cases ha : old.alive <;>
      simp_all [bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw]
    all_goals intro heq; simpa [← heq] using ha

@[simp] theorem getStream_iff {s sid st} : getStream s sid = .ok st ↔ s.streams[sid]? = some st := by
  unfold getStream
  cases h : s.streams[sid]? <;> simp

inductive Accesses : Command → Nat → Mode → Prop where
  | copyRead (src dst) : Accesses (.copy src dst) src .read
  | copyWrite (src dst) : Accesses (.copy src dst) dst .write
  | useRead (bid) : Accesses (.use bid) bid .read

def Holds (s : State) (bid : Nat) (loan : Loan) : Prop :=
  ∃ b, s.buffers[bid]? = some b ∧ b.alive = true ∧ loan ∈ b.loans

structure Invariant (s : State) : Prop where
  clocks : ∀ (sid : Nat) (st : Stream), s.streams[sid]? = some st → st.issued = st.completed + st.queue.length
  pending : ∀ (sid : Nat) (st : Stream), s.streams[sid]? = some st → ∀ (i : Nat) (cmd : Command), st.queue[i]? = some cmd →
    ∀ (bid : Nat) (mode : Mode), Accesses cmd bid mode → Holds s bid ⟨⟨sid,st.completed+i+1⟩,mode⟩

def ExtendsBuffers (s s' : State) : Prop := ∀ (bid : Nat) (b : Buffer), s.buffers[bid]? = some b →
  ∃ b' : Buffer, s'.buffers[bid]? = some b' ∧ b'.alive = b.alive ∧ ∀ l ∈ b.loans, l ∈ b'.loans

theorem holds_extend {s s' bid loan} (he : ExtendsBuffers s s') (hh : Holds s bid loan) :
    Holds s' bid loan := by
  obtain ⟨b,hb,ha,hl⟩ := hh
  obtain ⟨b',hb',ha',hl'⟩ := he bid b hb
  exact ⟨b',hb',ha'.trans ha,hl' loan hl⟩

theorem invariant_extend {s s'} (hi : Invariant s) (hst : s'.streams = s.streams)
    (he : ExtendsBuffers s s') : Invariant s' := by
  refine ⟨?_,?_⟩
  · intro sid st hget; exact hi.clocks sid st (by simpa [hst] using hget)
  · intro sid st hget i cmd hcmd bid mode hacc
    exact holds_extend he (hi.pending sid st (by simpa [hst] using hget) i cmd hcmd bid mode hacc)

theorem value_update_extends {s bid b value} (hb : s.buffers[bid]? = some b) :
    ExtendsBuffers s {s with buffers := s.buffers.set bid {b with value := value}} := by
  have hlt := (List.getElem?_eq_some_iff.mp hb).choose
  intro j old hold
  by_cases hj : j = bid
  · subst j
    have ho : old = b := by simpa [hb] using hold.symm
    subst old
    exact ⟨{b with value := value},by simp [List.getElem?_set_self hlt],rfl,fun _ h => h⟩
  · exact ⟨old,by simpa [List.getElem?_set_ne (Ne.symm hj)] using hold,rfl,fun _ h => h⟩

theorem loan_update_extends {s bid b loan} (hb : s.buffers[bid]? = some b) :
    ExtendsBuffers s {s with buffers := s.buffers.set bid {b with loans := loan::b.loans}} := by
  have hlt := (List.getElem?_eq_some_iff.mp hb).choose
  intro j old hold
  by_cases hj : j = bid
  · subst j
    have ho : old = b := by simpa [hb] using hold.symm
    subst old
    exact ⟨{b with loans := loan::b.loans},by simp [List.getElem?_set_self hlt],rfl,
      fun _ h => List.mem_cons_of_mem _ h⟩
  · exact ⟨old,by simpa [List.getElem?_set_ne (Ne.symm hj)] using hold,rfl,fun _ h => h⟩

theorem execute_frame {s cmd s'} (hs : execute s cmd = .ok s') :
    s'.streams = s.streams ∧ ExtendsBuffers s s' := by
  cases cmd with
  | wait t =>
    unfold execute at hs
    cases hc : complete s t <;> simp [hc,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at hs
    subst s'
    exact ⟨rfl,fun _ b hb => ⟨b,hb,rfl,fun _ h => h⟩⟩
  | use bid =>
    unfold execute at hs
    cases hb : getBuffer s bid with
    | error e => simp [hb,bind,Except.bind] at hs
    | ok b =>
      simp [hb,bind,Except.bind,pure,Except.pure] at hs
      subst s'
      exact ⟨rfl,fun _ b hb => ⟨b,hb,rfl,fun _ h => h⟩⟩
  | copy src dst =>
    unfold execute at hs
    cases ha : getBuffer s src with
    | error e => simp [ha,bind,Except.bind] at hs
    | ok a =>
      cases hb : getBuffer s dst with
      | error e => simp [ha,hb,bind,Except.bind] at hs
      | ok b =>
        simp [ha,hb,bind,Except.bind,pure,Except.pure] at hs
        subst s'
        exact ⟨rfl,value_update_extends (getBuffer_iff.mp hb).1⟩

theorem execute_invariant {s cmd s'} (hi : Invariant s) (hs : execute s cmd = .ok s') :
    Invariant s' :=
  invariant_extend hi (execute_frame hs).1 (execute_frame hs).2

theorem borrow_spec {s sid bid mode s'} (hs : borrow s sid bid mode = .ok s') :
    s'.streams = s.streams ∧ ExtendsBuffers s s' ∧ ∃ st,
      s.streams[sid]? = some st ∧ Holds s' bid ⟨⟨sid,st.issued+1⟩,mode⟩ := by
  unfold borrow at hs
  cases hst : getStream s sid with
  | error e => simp [hst,bind,Except.bind] at hs
  | ok st =>
    cases hb : getBuffer s bid with
    | error e => simp [hst,hb,bind,Except.bind] at hs
    | ok b =>
      by_cases hm : mayBorrow sid st mode b = true
      · simp [hst,hb,hm,bind,Except.bind,pure,Except.pure] at hs
        subst s'
        obtain ⟨hget,halive⟩ := getBuffer_iff.mp hb
        have hlt := (List.getElem?_eq_some_iff.mp hget).choose
        refine ⟨rfl,loan_update_extends hget,st,getStream_iff.mp hst,?_⟩
        exact ⟨{b with loans := ⟨⟨sid,st.issued+1⟩,mode⟩ :: b.loans},
          by simp [List.getElem?_set_self hlt],halive,by simp⟩
      · simp [hst,hb,hm,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs

theorem borrow_invariant {s sid bid mode s'} (hi : Invariant s)
    (hs : borrow s sid bid mode = .ok s') : Invariant s' :=
  invariant_extend hi (borrow_spec hs).1 (borrow_spec hs).2.1

theorem append_position {xs : List Command} {cmd actual : Command} {i : Nat}
    (h : (xs ++ [cmd])[i]? = some actual) :
    (i < xs.length ∧ xs[i]? = some actual) ∨ (i = xs.length ∧ actual = cmd) := by
  by_cases hb : i < xs.length
  · left; exact ⟨hb,by simpa [List.getElem?_append_left hb] using h⟩
  · rw [List.getElem?_append_right (by omega)] at h
    cases hd : i-xs.length with
    | zero => simp [hd] at h; exact Or.inr ⟨by omega,h.symm⟩
    | succ n => simp [hd] at h

/-- Appending a command needs a live loan for every access at the NEW ticket.
Raw enqueue is therefore not a rule with an unrestricted precondition. -/
theorem enqueue_invariant {s sid cmd s'} (hi : Invariant s)
    (hnew : ∀ st, s.streams[sid]? = some st → ∀ bid mode, Accesses cmd bid mode →
      Holds s bid ⟨⟨sid,st.issued+1⟩,mode⟩)
    (hs : enqueue s sid cmd = .ok s') : Invariant s' := by
  unfold enqueue at hs
  cases hst : getStream s sid with
  | error e => simp [hst,bind,Except.bind] at hs
  | ok st =>
    simp [hst,bind,Except.bind,pure,Except.pure] at hs
    subst s'
    have hget := getStream_iff.mp hst
    have hlt := (List.getElem?_eq_some_iff.mp hget).choose
    refine ⟨?_,?_⟩
    · intro j current hj
      by_cases he : j = sid
      · subst j
        have heq : {st with issued := st.issued+1,queue := st.queue ++ [cmd]} = current := by
          simpa [List.getElem?_set_self hlt] using hj
        subst current
        have hc := hi.clocks sid st hget
        simp only [List.length_append,List.length_singleton]
        omega
      · apply hi.clocks j current
        simpa [List.getElem?_set_ne (Ne.symm he)] using hj
    · intro j current hj i actual hcmd bid mode hacc
      by_cases he : j = sid
      · subst j
        have heq : {st with issued := st.issued+1,queue := st.queue ++ [cmd]} = current := by
          simpa [List.getElem?_set_self hlt] using hj
        subst current
        rcases append_position hcmd with ⟨_,hold⟩ | ⟨rfl,rfl⟩
        · exact hi.pending sid st hget i actual hold bid mode hacc
        · have hc := hi.clocks sid st hget
          have hl := hnew st hget bid mode hacc
          simpa [Holds,hc] using hl
      · apply hi.pending j current _ i actual hcmd bid mode hacc
        simpa [List.getElem?_set_ne (Ne.symm he)] using hj

theorem borrow_holds {s sid bid mode s' st} (hs : borrow s sid bid mode = .ok s')
    (hget : s'.streams[sid]? = some st) : Holds s' bid ⟨⟨sid,st.issued+1⟩,mode⟩ := by
  obtain ⟨hstreams,_,old,hold,hh⟩ := borrow_spec hs
  have heq : old = st := by simpa [hstreams,hold] using hget
  simpa [heq] using hh

theorem submitUse_invariant {s sid bid s'} (hi : Invariant s)
    (hs : submitUse s sid bid = .ok s') : Invariant s' := by
  unfold submitUse at hs
  cases hb : borrow s sid bid .read with
  | error e => simp [hb,bind,Except.bind] at hs
  | ok mid =>
    apply enqueue_invariant (borrow_invariant hi hb) _ (by simpa [hb,bind,Except.bind] using hs)
    intro st hget j mode hacc
    cases hacc
    exact borrow_holds hb hget

theorem submitCopy_invariant {s sid src dst s'} (hi : Invariant s)
    (hs : submitCopy s sid src dst = .ok s') : Invariant s' := by
  unfold submitCopy at hs
  by_cases heq : src = dst
  · simp [heq,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
  · cases ha : borrow s sid src .read with
    | error e => simp [heq,ha,bind,Except.bind] at hs
    | ok first =>
      cases hb : borrow first sid dst .write with
      | error e => simp [heq,ha,hb,bind,Except.bind] at hs
      | ok mid =>
        apply enqueue_invariant (borrow_invariant (borrow_invariant hi ha) hb) _
          (by simpa [heq,ha,hb,bind,Except.bind] using hs)
        intro st hget j mode hacc
        cases hacc with
        | copyRead =>
          have hfirst : first.streams[sid]? = some st := by simpa [(borrow_spec hb).1] using hget
          exact holds_extend (borrow_spec hb).2.1 (borrow_holds ha hfirst)
        | copyWrite => exact borrow_holds hb hget

theorem dependencies_invariant {s sid st} (hi : Invariant s)
    (hget : s.streams[sid]? = some st) (deps : List Ticket) :
    Invariant {s with streams := s.streams.set sid {st with dependencies := deps}} := by
  have hlt := (List.getElem?_eq_some_iff.mp hget).choose
  refine ⟨?_,?_⟩
  · intro j current hj
    by_cases he : j = sid
    · subst j
      have heq : {st with dependencies := deps} = current := by simpa [List.getElem?_set_self hlt] using hj
      subst current
      exact hi.clocks sid st hget
    · apply hi.clocks j current
      simpa [List.getElem?_set_ne (Ne.symm he)] using hj
  · intro j current hj i cmd hcmd bid mode hacc
    by_cases he : j = sid
    · subst j
      have heq : {st with dependencies := deps} = current := by simpa [List.getElem?_set_self hlt] using hj
      subst current
      exact hi.pending sid st hget i cmd hcmd bid mode hacc
    · apply hi.pending j current _ i cmd hcmd bid mode hacc
      simpa [List.getElem?_set_ne (Ne.symm he)] using hj

theorem waitStream_invariant {s sid id s'} (hi : Invariant s)
    (hs : waitStream s sid id = .ok s') : Invariant s' := by
  unfold waitStream at hs
  cases he : getEvent s id with
  | error e => simp [he,bind,Except.bind] at hs
  | ok t =>
    cases hq : enqueue s sid (.wait t) with
    | error e => simp [he,hq,bind,Except.bind] at hs
    | ok mid =>
      have hmid : Invariant mid := enqueue_invariant hi (by intro _ _ _ _ h; cases h) hq
      cases hst : getStream mid sid with
      | error e => simp [he,hq,hst,bind,Except.bind] at hs
      | ok st =>
        simp [he,hq,hst,bind,Except.bind,pure,Except.pure] at hs
        subst s'
        exact dependencies_invariant hmid (getStream_iff.mp hst) _

theorem record_invariant {s sid id s'} (hi : Invariant s)
    (hs : record s sid id = .ok s') : Invariant s' := by
  unfold record at hs
  cases hst : getStream s sid with
  | error e => simp [hst,bind,Except.bind] at hs
  | ok st =>
    by_cases hd : s.events.any (fun e => e.id == id) = true
    · simp [hst,hd,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
    · simp [hst,hd,bind,Except.bind,pure,Except.pure] at hs
      subst s'
      exact ⟨hi.clocks,hi.pending⟩

/-- A completed event cannot cover the ticket of a still-queued access. -/
theorem pending_not_covered {s sid st front i} (hst : s.streams[sid]? = some st)
    (hc : complete s front = true) : covers front ⟨sid,st.completed+i+1⟩ = false := by
  cases hcover : covers front ⟨sid,st.completed+i+1⟩ with
  | false => rfl
  | true =>
    have h := hcover
    simp only [covers,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
    obtain ⟨hstream,hseq⟩ := h
    have hdone : front.seq ≤ st.completed := by simpa [complete,hstream,hst] using hc
    omega

theorem await_invariant {s id s'} (hi : Invariant s)
    (hs : await s id = .ok s') : Invariant s' := by
  unfold await at hs
  cases ht : getEvent s id with
  | error e => simp [ht,bind,Except.bind] at hs
  | ok front =>
    cases hc : complete s front with
    | false => simp [ht,hc,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
    | true =>
      simp [ht,hc,bind,Except.bind,pure,Except.pure] at hs
      subst s'
      refine ⟨hi.clocks,?_⟩
      intro sid st hst i cmd hcmd bid mode hacc
      obtain ⟨b,hb,ha,hl⟩ := hi.pending sid st hst i cmd hcmd bid mode hacc
      refine ⟨{b with loans := b.loans.filter (fun l => !covers front l.ticket)},?_,ha,?_⟩
      · simp [List.getElem?_map,hb]
      · apply List.mem_filter.mpr
        exact ⟨hl,by simp [pending_not_covered hst hc]⟩

theorem hostWrite_invariant {s bid value s'} (hi : Invariant s)
    (hs : hostWrite s bid value = .ok s') : Invariant s' := by
  unfold hostWrite at hs
  cases hb : getBuffer s bid with
  | error e => simp [hb,bind,Except.bind] at hs
  | ok b =>
    by_cases hempty : b.loans.isEmpty = true
    · simp [hb,hempty,bind,Except.bind,pure,Except.pure] at hs
      subst s'
      exact invariant_extend hi rfl (value_update_extends (getBuffer_iff.mp hb).1)
    · simp [hb,hempty,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs

theorem reclaim_invariant {s bid s'} (hi : Invariant s)
    (hs : reclaim s bid = .ok s') : Invariant s' := by
  unfold reclaim at hs
  cases hb : getBuffer s bid with
  | error e => simp [hb,bind,Except.bind] at hs
  | ok b =>
    by_cases hempty : b.loans.isEmpty = true
    · simp [hb,hempty,bind,Except.bind,pure,Except.pure] at hs
      subst s'
      have hnil : b.loans = [] := by simpa using hempty
      have hget := (getBuffer_iff.mp hb).1
      refine ⟨hi.clocks,?_⟩
      intro sid st hst i cmd hcmd j mode hacc
      obtain ⟨old,hold,ha,hl⟩ := hi.pending sid st hst i cmd hcmd j mode hacc
      by_cases hj : j = bid
      · subst j
        have heq : old = b := by simpa [hget] using hold.symm
        subst old
        simp [hnil] at hl
      · exact ⟨old,by simpa [List.getElem?_set_ne (Ne.symm hj)] using hold,ha,hl⟩
    · simp [hb,hempty,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs

theorem reclaim_of_holds {s bid loan} (hh : Holds s bid loan) :
    reclaim s bid = .error .outstandingLoan := by
  obtain ⟨b,hb,ha,hl⟩ := hh
  have hn : b.loans.isEmpty = false := by
    cases hnil : b.loans with
    | nil => simp [hnil] at hl
    | cons l ls => rfl
  exact reclaim_rejects_loan (getBuffer_iff.mpr ⟨hb,ha⟩) hn

theorem pop_invariant {s : State} {sid : Nat} {st : Stream} {cmd : Command}
    (hi : Invariant s) (hst : s.streams[sid]? = some st)
    (hhead : st.queue.head? = some cmd) :
    Invariant {s with streams := s.streams.set sid {st with completed := st.completed+1,queue := st.queue.drop 1}} := by
  have hlt := (List.getElem?_eq_some_iff.mp hst).choose
  have hnonempty : 0 < st.queue.length := by
    cases hq : st.queue with
    | nil => simp [hq] at hhead
    | cons c cs => simp
  refine ⟨?_,?_⟩
  · intro j current hj
    by_cases he : j = sid
    · subst j
      have heq : {st with completed := st.completed+1,queue := st.queue.drop 1} = current := by
        simpa [List.getElem?_set_self hlt] using hj
      subst current
      have hc := hi.clocks sid st hst
      simp only [List.length_drop]
      omega
    · apply hi.clocks j current
      simpa [List.getElem?_set_ne (Ne.symm he)] using hj
  · intro j current hj i actual hcmd bid mode hacc
    by_cases he : j = sid
    · subst j
      have heq : {st with completed := st.completed+1,queue := st.queue.drop 1} = current := by
        simpa [List.getElem?_set_self hlt] using hj
      subst current
      have hold : st.queue[i+1]? = some actual := by simpa [List.getElem?_drop,Nat.add_comm] using hcmd
      have hl := hi.pending sid st hst (i+1) actual hold bid mode hacc
      simpa [Holds,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hl
    · apply hi.pending j current _ i actual hcmd bid mode hacc
      simpa [List.getElem?_set_ne (Ne.symm he)] using hj

theorem deviceStep_invariant {s sid s'} (hi : Invariant s)
    (hs : deviceStep s sid = .ok s') : Invariant s' := by
  unfold deviceStep at hs
  cases hst : getStream s sid with
  | error e => simp [hst,bind,Except.bind] at hs
  | ok st =>
    cases hhead : st.queue.head? with
    | none => simp [hst,hhead,bind,Except.bind] at hs
    | some cmd =>
      cases hex : execute s cmd with
      | error e => simp [hst,hhead,hex,bind,Except.bind] at hs
      | ok mid =>
        simp [hst,hhead,hex,bind,Except.bind,pure,Except.pure] at hs
        subst s'
        have hget : mid.streams[sid]? = some st := by
          simpa [(execute_frame hex).1] using getStream_iff.mp hst
        simpa using pop_invariant (execute_invariant hi hex) hget hhead

theorem execute_ready {s : State} {sid : Nat} {st : Stream} {cmd : Command}
    (hi : Invariant s) (hst : s.streams[sid]? = some st)
    (hhead : st.queue.head? = some cmd)
    (hwait : ∀ t, cmd = .wait t → complete s t = true) : ∃ mid, execute s cmd = .ok mid := by
  have hidx : st.queue[0]? = some cmd := by
    have heq : st.queue[0]? = st.queue.head? := by cases st.queue <;> rfl
    rw [heq]; exact hhead
  cases cmd with
  | copy src dst =>
    obtain ⟨a,ha,haa,_⟩ := hi.pending sid st hst 0 (.copy src dst) hidx src .read (.copyRead ..)
    obtain ⟨b,hb,hba,_⟩ := hi.pending sid st hst 0 (.copy src dst) hidx dst .write (.copyWrite ..)
    have hga := getBuffer_iff.mpr ⟨ha,haa⟩
    have hgb := getBuffer_iff.mpr ⟨hb,hba⟩
    exact ⟨{s with buffers := s.buffers.set dst {b with value := a.value}},
      by simp [execute,hga,hgb,bind,Except.bind,pure,Except.pure]⟩
  | use bid =>
    obtain ⟨b,hb,hba,_⟩ := hi.pending sid st hst 0 (.use bid) hidx bid .read (.useRead ..)
    have hgb := getBuffer_iff.mpr ⟨hb,hba⟩
    exact ⟨s,by simp [execute,hgb,bind,Except.bind,pure,Except.pure]⟩
  | wait t => exact ⟨s,by simp [execute,hwait t rfl,pure,Except.pure]⟩

/-- A queued command cannot fail from invalid/freed memory. A wait still requires
actual completion; no completion or scheduling fairness is assumed here. -/
theorem deviceStep_ready {s : State} {sid : Nat} {st : Stream} {cmd : Command}
    (hi : Invariant s) (hst : s.streams[sid]? = some st)
    (hhead : st.queue.head? = some cmd)
    (hwait : ∀ t, cmd = .wait t → complete s t = true) : ∃ s', deviceStep s sid = .ok s' := by
  obtain ⟨mid,hex⟩ := execute_ready hi hst hhead hwait
  refine ⟨{mid with streams := mid.streams.set sid {st with completed := st.completed+1,queue := st.queue.drop 1}},?_⟩
  simp [deviceStep,getStream_iff.mpr hst,hhead,hex,bind,Except.bind,pure,Except.pure]

/-- A queued device action either succeeds or is an actual not-yet-complete
event wait. Invalid/freed-buffer failures are excluded by the lifetime invariant. -/
theorem deviceStep_safe {s : State} {sid : Nat} {st : Stream} {cmd : Command}
    (hi : Invariant s) (hst : s.streams[sid]? = some st) (hhead : st.queue.head? = some cmd) :
    (∃ s', deviceStep s sid = .ok s') ∨ deviceStep s sid = .error .notComplete := by
  cases cmd with
  | copy src dst => exact Or.inl (deviceStep_ready hi hst hhead (by intro t h; cases h))
  | use bid => exact Or.inl (deviceStep_ready hi hst hhead (by intro t h; cases h))
  | wait front =>
    cases hc : complete s front with
    | true =>
      left
      apply deviceStep_ready hi hst hhead
      intro t heq
      cases heq
      exact hc
    | false =>
      right
      simp [deviceStep,getStream_iff.mpr hst,hhead,execute,hc,bind,Except.bind,
        throw,throwThe,MonadExceptOf.throw]

theorem initial_invariant (streamCount : Nat) (values : List Nat) :
    Invariant (initial streamCount values) := by
  refine ⟨?_,?_⟩
  · intro sid st hst
    have hmem : st ∈ List.replicate streamCount ({} : Stream) := List.mem_of_getElem? hst
    have heq := (List.mem_replicate.mp hmem).2
    subst st
    rfl
  · intro sid st hst i cmd hcmd bid mode hacc
    have hmem : st ∈ List.replicate streamCount ({} : Stream) := List.mem_of_getElem? hst
    have heq := (List.mem_replicate.mp hmem).2
    subst st
    simp at hcmd

theorem step_invariant {s a s'} (hi : Invariant s) (hs : step s a = .ok s') : Invariant s' := by
  cases a with
  | copy sid src dst => exact submitCopy_invariant hi hs
  | use sid bid => exact submitUse_invariant hi hs
  | record sid id => exact record_invariant hi hs
  | wait sid id => exact waitStream_invariant hi hs
  | device sid => exact deviceStep_invariant hi hs
  | acquire id => exact await_invariant hi hs
  | reclaim bid => exact reclaim_invariant hi hs
  | write bid value => exact hostWrite_invariant hi hs

theorem steps_invariant {s s'} (hi : Invariant s) (hs : Steps s s') : Invariant s' := by
  induction hs with
  | refl => exact hi
  | next a hstep hrest ih => exact ih (step_invariant hi hstep)

/-- Main lifetime consequence: any pending access in any stream rejects host
reclamation, derived from the queue/loan invariant rather than a loan premise. -/
theorem pending_reclaim_rejected {s : State} {sid i bid : Nat} {st : Stream} {cmd : Command} {mode : Mode}
    (hi : Invariant s) (hst : s.streams[sid]? = some st) (hcmd : st.queue[i]? = some cmd)
    (hacc : Accesses cmd bid mode) : reclaim s bid = .error .outstandingLoan :=
  reclaim_of_holds (hi.pending sid st hst i cmd hcmd bid mode hacc)

theorem reachable_pending_reclaim_rejected {streamCount : Nat} {values : List Nat} {s : State}
    {sid i bid : Nat} {st : Stream} {cmd : Command} {mode : Mode}
    (hs : Steps (initial streamCount values) s) (hst : s.streams[sid]? = some st)
    (hcmd : st.queue[i]? = some cmd) (hacc : Accesses cmd bid mode) :
    reclaim s bid = .error .outstandingLoan :=
  pending_reclaim_rejected (steps_invariant (initial_invariant _ _) hs) hst hcmd hacc

theorem hostWrite_of_holds {s bid loan value} (hh : Holds s bid loan) :
    hostWrite s bid value = .error .outstandingLoan := by
  obtain ⟨b,hb,ha,hl⟩ := hh
  have hn : b.loans.isEmpty = false := by
    cases hnil : b.loans with
    | nil => simp [hnil] at hl
    | cons l ls => rfl
  have hg := getBuffer_iff.mpr ⟨hb,ha⟩
  simp [hostWrite,hg,hn,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

theorem reachable_pending_hostWrite_rejected {streamCount : Nat} {values : List Nat} {s : State}
    {sid i bid value : Nat} {st : Stream} {cmd : Command} {mode : Mode}
    (hs : Steps (initial streamCount values) s) (hst : s.streams[sid]? = some st)
    (hcmd : st.queue[i]? = some cmd) (hacc : Accesses cmd bid mode) :
    hostWrite s bid value = .error .outstandingLoan :=
  hostWrite_of_holds ((steps_invariant (initial_invariant _ _) hs).pending sid st hst i cmd hcmd bid mode hacc)

end Ptx.Async
