import Ptx.Async.Invariant

/-! Every successful public action preserves the allocated buffer count. This
is proved from the real interpreter and permits same-domain physical heap updates.
-/
namespace Ptx.Async

private theorem borrow_length {s sid bid mode s'} (hs : borrow s sid bid mode = .ok s') :
    s'.buffers.length = s.buffers.length := by
  unfold borrow at hs
  simp only [bind,Except.bind,Pure.pure,Except.pure] at hs
  repeat first | (solve | simp_all) | split at hs
  all_goals
    have hstate := Except.ok.inj hs
    cases hstate
    simp_all

private theorem enqueue_length {s sid cmd s'} (hs : enqueue s sid cmd = .ok s') :
    s'.buffers.length = s.buffers.length := by
  unfold enqueue at hs
  simp only [bind,Except.bind,Pure.pure,Except.pure] at hs
  repeat first | (solve | simp_all) | split at hs
  all_goals
    have hstate := Except.ok.inj hs
    cases hstate
    simp_all

private theorem record_length {s sid event s'} (hs : record s sid event = .ok s') :
    s'.buffers.length = s.buffers.length := by
  unfold record at hs
  simp only [bind,Except.bind,Pure.pure,Except.pure] at hs
  repeat first | (solve | simp_all) | split at hs
  all_goals
    have hstate := Except.ok.inj hs
    cases hstate
    simp_all

private theorem execute_length {s cmd s'} (hs : execute s cmd = .ok s') :
    s'.buffers.length = s.buffers.length := by
  cases cmd <;> simp only [execute,bind,Except.bind,Pure.pure,Except.pure] at hs
  all_goals repeat first | (solve | simp_all) | split at hs
  all_goals
    have hstate := Except.ok.inj hs
    cases hstate
    simp_all

private theorem reclaim_length {s bid s'} (hs : reclaim s bid = .ok s') :
    s'.buffers.length = s.buffers.length := by
  unfold reclaim at hs
  simp only [bind,Except.bind,Pure.pure,Except.pure] at hs
  repeat first | (solve | simp_all) | split at hs
  all_goals
    have hstate := Except.ok.inj hs
    cases hstate
    simp_all

private theorem hostWrite_length {s bid value s'} (hs : hostWrite s bid value = .ok s') :
    s'.buffers.length = s.buffers.length := by
  unfold hostWrite at hs
  simp only [bind,Except.bind,Pure.pure,Except.pure] at hs
  repeat first | (solve | simp_all) | split at hs
  all_goals
    have hstate := Except.ok.inj hs
    cases hstate
    simp_all

private theorem await_length {s event s'} (hs : await s event = .ok s') :
    s'.buffers.length = s.buffers.length := by
  unfold await at hs
  simp only [bind,Except.bind,Pure.pure,Except.pure] at hs
  repeat first | (solve | simp_all) | split at hs
  all_goals
    have hstate := Except.ok.inj hs
    cases hstate
    simp_all

private theorem submitUse_length {s sid bid s'} (hs : submitUse s sid bid = .ok s') :
    s'.buffers.length = s.buffers.length := by
  unfold submitUse at hs
  cases hb : borrow s sid bid .read with
  | error e => simp [hb,bind,Except.bind] at hs
  | ok mid =>
    have hq : enqueue mid sid (.use bid) = .ok s' := by simpa [hb,bind,Except.bind] using hs
    exact (enqueue_length hq).trans (borrow_length hb)

private theorem submitAccess_length {s sid bid mode s'} (hs : submitAccess s sid bid mode = .ok s') :
    s'.buffers.length = s.buffers.length := by
  unfold submitAccess at hs
  cases hb : borrow s sid bid mode with
  | error e => simp [hb,bind,Except.bind] at hs
  | ok mid =>
    have hq : enqueue mid sid (.access bid mode) = .ok s' := by simpa [hb,bind,Except.bind] using hs
    exact (enqueue_length hq).trans (borrow_length hb)

private theorem submitCopy_length {s sid src dst s'} (hs : submitCopy s sid src dst = .ok s') :
    s'.buffers.length = s.buffers.length := by
  unfold submitCopy at hs
  by_cases ha : src == dst
  · simp [ha,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
  · simp only [ha,Bool.false_eq_true,ite_false] at hs
    cases hb : borrow s sid src .read with
    | error e => simp [hb,bind,Except.bind] at hs
    | ok mid =>
      cases hc : borrow mid sid dst .write with
      | error e => simp [hb,hc,bind,Except.bind] at hs
      | ok last =>
        have hq : enqueue last sid (.copy src dst) = .ok s' := by simpa [hb,hc,bind,Except.bind] using hs
        exact (enqueue_length hq).trans ((borrow_length hc).trans (borrow_length hb))

private theorem waitStream_length {s sid event s'} (hs : waitStream s sid event = .ok s') :
    s'.buffers.length = s.buffers.length := by
  unfold waitStream at hs
  cases he : getEvent s event with
  | error e => simp [he,bind,Except.bind] at hs
  | ok ticket =>
    cases hq : enqueue s sid (.wait ticket) with
    | error e => simp [he,hq,bind,Except.bind] at hs
    | ok mid =>
      have hlen := enqueue_length hq
      simp only [he,hq,bind,Except.bind,Pure.pure,Except.pure] at hs
      repeat first | (solve | simp_all) | split at hs
      all_goals
        have hstate := Except.ok.inj hs
        cases hstate
        exact hlen
  all_goals
    have hstate := Except.ok.inj hs
    cases hstate
    simp_all

private theorem deviceStep_length {s sid s'} (hs : deviceStep s sid = .ok s') :
    s'.buffers.length = s.buffers.length := by
  unfold deviceStep at hs
  cases ht : getStream s sid with
  | error e => simp [ht,bind,Except.bind] at hs
  | ok stream =>
    cases hq : stream.queue.head? with
    | none => simp [ht,hq,bind,Except.bind] at hs
    | some cmd =>
      cases hx : execute s cmd with
      | error e => simp [ht,hq,hx,bind,Except.bind] at hs
      | ok mid =>
        have hlen := execute_length hx
        simp [ht,hq,hx,bind,Except.bind,Pure.pure,Except.pure] at hs
        cases hs
        exact hlen

theorem step_buffers_length {s action s'} (hs : step s action = .ok s') :
    s'.buffers.length = s.buffers.length := by
  cases action with
  | copy _ _ _ => exact submitCopy_length hs
  | use _ _ => exact submitUse_length hs
  | access _ _ _ => exact submitAccess_length hs
  | record _ _ => exact record_length hs
  | wait _ _ => exact waitStream_length hs
  | device _ => exact deviceStep_length hs
  | acquire _ => exact await_length hs
  | reclaim _ => exact reclaim_length hs
  | write _ _ => exact hostWrite_length hs

theorem steps_buffers_length {s s'} (hs : Steps s s') : s'.buffers.length = s.buffers.length := by
  induction hs with
  | refl => rfl
  | next action hstep _ ih => exact ih.trans (step_buffers_length hstep)

end Ptx.Async
