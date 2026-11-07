import Ptx.Event.Execution

/-! Generic finite-trace reconstruction. A deterministic oracle-driven thread
cannot have two different successful completed traces from the same initial
state. Counts are arbitrary naturals; no fuel bound or schedule enumeration is
assumed. This is not a termination theorem. -/
namespace Ptx.Event

theorem run_add (ctx : Context) (oracle : Oracle) (code : List Instr) (n m : Nat) (s : State) :
    run ctx oracle code (n+m) s =
      (run ctx oracle code n s).bind (fun first =>
        (run ctx oracle code m first.1).bind (fun last => .ok (last.1, first.2 ++ last.2))) := by
  induction n generalizing s with
  | zero => cases hr : run ctx oracle code m s <;> simp [run, hr, Except.bind]
  | succ n ih =>
    cases hs : step ctx oracle code s with
    | error e => simp [Nat.succ_add, run, hs, Except.bind]
    | ok first =>
      rcases first with ⟨mid, events⟩
      rw [Nat.succ_add, run, hs]
      simp only [Except.bind]
      rw [ih]
      cases hr : run ctx oracle code n mid with
      | error e => simp [run, hs, hr, Except.bind]
      | ok result =>
        rcases result with ⟨next, rest⟩
        simp [run, hs, hr, Except.bind]
        cases run ctx oracle code m next <;> rfl

theorem run_after_done {ctx oracle code s} (hd : s.thread.status = .done) (n : Nat) :
    run ctx oracle code (n+1) s = .error .blocked := by
  simp [run, step, hd, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

theorem completed_suffix_zero {ctx oracle code k n s last events final allEvents}
    (hk : run ctx oracle code k s = .ok (last, events)) (hd : last.thread.status = .done)
    (hn : run ctx oracle code (k+n) s = .ok (final, allEvents)) : n = 0 := by
  rw [run_add, hk] at hn
  simp only [Except.bind] at hn
  cases n with
  | zero => rfl
  | succ n => simp [run_after_done hd n] at hn

theorem complete_run_unique {ctx oracle code n k s a b ea eb}
    (hn : run ctx oracle code n s = .ok (a, ea)) (ha : a.thread.status = .done)
    (hk : run ctx oracle code k s = .ok (b, eb)) (hb : b.thread.status = .done) :
    n = k ∧ a = b ∧ ea = eb := by
  have hcount : n = k := by
    rcases Nat.le_total n k with hle | hle
    · obtain ⟨d, hkd⟩ := Nat.exists_eq_add_of_le hle
      have hz := completed_suffix_zero hn ha (hkd ▸ hk)
      omega
    · obtain ⟨d, hnd⟩ := Nat.exists_eq_add_of_le hle
      have hz := completed_suffix_zero hk hb (hnd ▸ hn)
      omega
  subst k
  exact ⟨rfl, Prod.mk.inj (Except.ok.inj (hn.symm.trans hk))⟩

end Ptx.Event
