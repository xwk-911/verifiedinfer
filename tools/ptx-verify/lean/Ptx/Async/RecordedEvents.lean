import Ptx.Hopper.CompletionBridge

/-! Recorded frontiers persist through the existing checked protocol. A new
record cannot replace an existing event. This does not assert completion of
the recorded work; acquisition still checks the real device counter.
-/
namespace Ptx.Async

theorem getEvent_iff {s id ticket} : getEvent s id = .ok ticket ↔
    ∃ entry, s.events.find? (fun event => event.id == id) = some entry ∧ entry.ticket = ticket := by
  unfold getEvent
  cases he : s.events.find? (fun event => event.id == id) with
  | none => simp [bind,Except.bind]
  | some entry => simp [bind,Except.bind,pure,Except.pure]

theorem event_fresh_invalid {s id} (hf : s.events.any (fun entry => entry.id == id) = false) :
    getEvent s id = .error .invalidEvent := by
  have hn : s.events.find? (fun entry => entry.id == id) = none := by
    cases he : s.events.find? (fun entry => entry.id == id) with
    | none => rfl
    | some entry =>
      have ht := List.any_eq_true.mpr ⟨entry,List.mem_of_find?_eq_some he,List.find?_some he⟩
      rw [hf] at ht
      cases ht
  simp [getEvent,hn,bind,Except.bind]

theorem record_preserves_existing_event {s next sid id event ticket}
    (hs : record s sid id = .ok next) (he : getEvent s event = .ok ticket) : getEvent next event = .ok ticket := by
  obtain ⟨entry,hfind,hvalue⟩ := getEvent_iff.mp he
  unfold record at hs
  cases hst : getStream s sid with
  | error error => simp [hst,bind,Except.bind] at hs
  | ok st =>
    by_cases hf : s.events.any (fun e => e.id == id) = true
    · simp [hst,hf,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
    · have hne : id ≠ event := by
        intro eq
        subst id
        have hpred : (entry.id == event) = true := List.find?_some (p := fun e : Event => e.id == event) hfind
        have hex : s.events.any (fun e => e.id == event) = true :=
          List.any_eq_true.mpr ⟨entry,List.mem_of_find?_eq_some hfind,hpred⟩
        exact hf hex
      simp [hst,hf,bind,Except.bind,pure,Except.pure] at hs
      subst next
      apply getEvent_iff.mpr
      exact ⟨entry,by simpa [List.find?_cons,hne] using hfind,hvalue⟩

theorem execute_preserves_events {s next command} (hs : execute s command = .ok next) : next.events = s.events := by
  cases command <;> unfold execute at hs <;> simp only [bind,Except.bind,pure,Except.pure] at hs
  all_goals repeat first | (solve | simp_all) | split at hs
  all_goals cases Except.ok.inj hs; rfl

theorem deviceStep_preserves_events {s next sid} (hs : deviceStep s sid = .ok next) : next.events = s.events := by
  unfold deviceStep at hs
  cases hg : getStream s sid with
  | error error => simp [hg,bind,Except.bind] at hs
  | ok stream =>
    cases hh : stream.queue.head? with
    | none => simp [hg,hh,bind,Except.bind] at hs
    | some command =>
      cases hr : execute s command with
      | error error => simp [hg,hh,hr,bind,Except.bind] at hs
      | ok mid =>
        simp [hg,hh,hr,bind,Except.bind,pure,Except.pure] at hs
        subst next
        change mid.events = s.events
        exact execute_preserves_events hr

theorem host_preserves_recorded_event {s next event ticket} (action : Ptx.Hopper.Progress.Bridge.HostAction)
    (hs : step s action.action = .ok next) (he : getEvent s event = .ok ticket) : getEvent next event = .ok ticket := by
  cases action with
  | record sid id => exact record_preserves_existing_event hs he
  | acquire id | reclaim id | write id value =>
    have hh : next.events = s.events := by
      first | change await s id = .ok next at hs | change reclaim s id = .ok next at hs | change hostWrite s id value = .ok next at hs
      first | unfold await at hs | unfold reclaim at hs | unfold hostWrite at hs
      simp only [bind,Except.bind,pure,Except.pure] at hs
      repeat first | (solve | simp_all) | split at hs
      all_goals cases Except.ok.inj hs; rfl
    simpa only [getEvent,hh] using he

end Ptx.Async
