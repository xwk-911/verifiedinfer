import Ptx.Async.CompletionClock

/-! Loan preservation in the executable protocol. Acquisition can drop only
complete tickets; successful host writes/reclamation cannot invalidate a loan
held by another operation. -/
namespace Ptx.Async

theorem deviceStep_extends {s sid s'} (hs : deviceStep s sid = .ok s') : ExtendsBuffers s s' := by
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
        exact (execute_frame hex).2

theorem deviceStep_complete_monotone {s sid s' ticket}
    (hs : deviceStep s sid = .ok s') (hc : complete s ticket = true) : complete s' ticket = true := by
  obtain ⟨st,hst,hshape⟩ := deviceStep_streams hs
  have hget := getStream_iff.mp hst
  have hlt := (List.getElem?_eq_some_iff.mp hget).choose
  by_cases he : ticket.stream = sid
  · have hb : ticket.seq ≤ st.completed := by simpa [complete,he,hget] using hc
    have hn : ticket.seq ≤ st.completed+1 := by omega
    simpa [complete,hshape,he,List.getElem?_set_self hlt] using hn
  · simpa [complete,hshape,List.getElem?_set_ne (Ne.symm he)] using hc

theorem await_incomplete_holds {s event s' bid loan}
    (hs : await s event = .ok s') (hh : Holds s bid loan) (hn : complete s loan.ticket ≠ true) : Holds s' bid loan := by
  obtain ⟨frontier,he,hc⟩ := await_requires_completion hs
  have hstate : s' = {s with buffers := s.buffers.map (fun b => {b with loans := b.loans.filter (fun l => !covers frontier l.ticket)})} := by
    simpa [await,he,hc,bind,Except.bind,pure,Except.pure] using hs.symm
  obtain ⟨b,hb,ha,hl⟩ := hh
  have hcover : covers frontier loan.ticket = false := by
    cases h : covers frontier loan.ticket with
    | false => rfl
    | true => exact False.elim (hn (covered_complete hc h))
  refine ⟨{b with loans := b.loans.filter (fun l => !covers frontier l.ticket)},?_,ha,?_⟩
  · simp [hstate,List.getElem?_map,hb]
  · simp [hl,hcover]

theorem record_holds {s sid event s' bid loan} (hs : record s sid event = .ok s')
    (hh : Holds s bid loan) : Holds s' bid loan := by
  unfold record at hs
  simp only [bind,Except.bind,Pure.pure,Except.pure] at hs
  repeat first | (solve | simp_all) | split at hs
  all_goals cases Except.ok.inj hs; exact hh

theorem hostWrite_extends {s bid value s'} (hs : hostWrite s bid value = .ok s') : ExtendsBuffers s s' := by
  unfold hostWrite at hs
  cases hb : getBuffer s bid with
  | error e => simp [hb,bind,Except.bind] at hs
  | ok b =>
    by_cases hempty : b.loans.isEmpty = true
    · simp [hb,hempty,bind,Except.bind,pure,Except.pure] at hs
      subst s'
      exact value_update_extends (getBuffer_iff.mp hb).1
    · simp [hb,hempty,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs

theorem reclaim_holds {s bid s' other loan} (hs : reclaim s bid = .ok s')
    (hh : Holds s other loan) : Holds s' other loan := by
  have hne : other ≠ bid := by
    intro heq
    subst other
    rw [reclaim_of_holds hh] at hs
    cases hs
  unfold reclaim at hs
  cases hb : getBuffer s bid with
  | error e => simp [hb,bind,Except.bind] at hs
  | ok b =>
    by_cases hempty : b.loans.isEmpty = true
    · simp [hb,hempty,bind,Except.bind,pure,Except.pure] at hs
      subst s'
      obtain ⟨old,hold,ha,hl⟩ := hh
      exact ⟨old,by simpa [List.getElem?_set_ne (Ne.symm hne)] using hold,ha,hl⟩
    · simp [hb,hempty,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs

end Ptx.Async
