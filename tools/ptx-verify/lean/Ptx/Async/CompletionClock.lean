import Ptx.Async.Invariant

/-! Exact counter changes of the existing interpreter. In particular, one
device action can complete only its next FIFO ticket, and acquiring a recorded
frontier can return only tickets already complete at that frontier. -/
namespace Ptx.Async

theorem deviceStep_streams {s sid s'} (hs : deviceStep s sid = .ok s') :
    ∃ st, getStream s sid = .ok st ∧
      s'.streams = s.streams.set sid {st with completed := st.completed+1, queue := st.queue.drop 1} := by
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
        exact ⟨st,rfl,by simp only [(execute_frame hex).1,List.drop_one]⟩

theorem deviceStep_new_completion {s sid s' ticket}
    (hs : deviceStep s sid = .ok s') (hc : complete s' ticket = true) :
    complete s ticket = true ∨ ∃ st, getStream s sid = .ok st ∧ ticket = ⟨sid,st.completed+1⟩ := by
  by_cases hold : complete s ticket = true
  · exact .inl hold
  right
  obtain ⟨st,hst,hshape⟩ := deviceStep_streams hs
  have hget := getStream_iff.mp hst
  have hlt := (List.getElem?_eq_some_iff.mp hget).choose
  by_cases he : ticket.stream = sid
  · have hnew : ticket.seq ≤ st.completed+1 := by
      simpa [complete,hshape,he,List.getElem?_set_self hlt] using hc
    have hnot : ¬ticket.seq ≤ st.completed := by simpa [complete,he,hget] using hold
    refine ⟨st,hst,?_⟩
    have hseq : ticket.seq = st.completed+1 := by omega
    cases ticket
    simp_all
  · have hsame : complete s' ticket = complete s ticket := by
      simp [complete,hshape,List.getElem?_set_ne (Ne.symm he)]
    exact False.elim (hold (hsame ▸ hc))

theorem covered_complete {s frontier ticket} (hc : complete s frontier = true)
    (hcover : covers frontier ticket = true) : complete s ticket = true := by
  simp only [covers,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hcover
  cases hget : s.streams[frontier.stream]? with
  | none => simp [complete,hget] at hc
  | some st =>
    have hbound : frontier.seq ≤ st.completed := by simpa [complete,hget] using hc
    simpa [complete,← hcover.1,hget] using Nat.le_trans hcover.2 hbound

theorem acquired_covered_complete {s event s' frontier ticket}
    (ha : await s event = .ok s') (he : getEvent s event = .ok frontier)
    (hcover : covers frontier ticket = true) : complete s ticket = true := by
  obtain ⟨actual,hactual,hc⟩ := await_requires_completion ha
  have ht : frontier = actual := by simpa only [he,Except.ok.injEq] using hactual
  subst actual
  exact covered_complete hc hcover

theorem await_removed_loan_complete {s event s' bid before after loan}
    (ha : await s event = .ok s') (hb : getBuffer s bid = .ok before)
    (hb' : getBuffer s' bid = .ok after) (hl : loan ∈ before.loans) (hgone : loan ∉ after.loans) :
    complete s loan.ticket = true := by
  obtain ⟨frontier,he,hc⟩ := await_requires_completion ha
  have hstate : s' = {s with buffers := s.buffers.map (fun b => {b with loans := b.loans.filter (fun l => !covers frontier l.ticket)})} := by
    simpa [await,he,hc,bind,Except.bind,pure,Except.pure] using ha.symm
  have hget := (getBuffer_iff.mp hb).1
  have hget' := (getBuffer_iff.mp hb').1
  have heq : after = {before with loans := before.loans.filter (fun l => !covers frontier l.ticket)} := by
    simpa [hstate,List.getElem?_map,hget] using hget'.symm
  have hcover : covers frontier loan.ticket = true := by
    by_cases h : covers frontier loan.ticket = true
    · exact h
    · have hmem : loan ∈ after.loans := by simp [heq,hl,h]
      exact False.elim (hgone hmem)
  exact covered_complete hc hcover

end Ptx.Async
