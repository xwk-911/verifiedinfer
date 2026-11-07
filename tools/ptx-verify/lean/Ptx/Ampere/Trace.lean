import Ptx.Ampere.Thread

/-! Finite source-run decomposition and complete trace reconstruction rules.
Counts are arbitrary; these rules neither bound fuel nor assert termination.
The full Ampere state, including its pending copy ledger, is preserved. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

theorem run_add (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) (n m : Nat) (s : State) :
    run ctx oracle code (n+m) s = (run ctx oracle code n s).bind (fun first =>
      (run ctx oracle code m first.1).bind (fun last => .ok (last.1,first.2 ++ last.2))) := by
  induction n generalizing s with
  | zero => cases hr : run ctx oracle code m s <;> simp [run,hr,Except.bind]
  | succ n ih =>
    cases hs : step ctx oracle code s with
    | error fault => simp [Nat.succ_add,run,hs,Except.bind]
    | ok first =>
      rcases first with ⟨mid,events⟩
      rw [Nat.succ_add,run,hs]
      simp only [Except.bind]
      rw [ih]
      cases hr : run ctx oracle code n mid with
      | error fault => simp [run,hs,hr,Except.bind]
      | ok result =>
        rcases result with ⟨next,rest⟩
        simp [run,hs,hr,Except.bind]
        cases run ctx oracle code m next <;> rfl


theorem run_done_suffix {ctx oracle code s} (hd : s.scalar.core.thread.status = .done) (n : Nat) :
    run ctx oracle code (n+1) s = .error .blocked := by
  simp [run,step,hd,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

theorem completed_suffix_zero {ctx oracle code k n s last events final allEvents}
    (hk : run ctx oracle code k s = .ok (last,events)) (hd : last.scalar.core.thread.status = .done)
    (hn : run ctx oracle code (k+n) s = .ok (final,allEvents)) : n = 0 := by
  rw [run_add,hk] at hn
  simp only [Except.bind] at hn
  cases n with
  | zero => rfl
  | succ n => simp [run_done_suffix hd n] at hn

theorem complete_run_unique {ctx oracle code n k s a b ea eb}
    (hn : run ctx oracle code n s = .ok (a,ea)) (ha : a.scalar.core.thread.status = .done)
    (hk : run ctx oracle code k s = .ok (b,eb)) (hb : b.scalar.core.thread.status = .done) :
    n = k ∧ a = b ∧ ea = eb := by
  have hcount : n = k := by
    rcases Nat.le_total n k with hle | hle
    · obtain ⟨d,hkd⟩ := Nat.exists_eq_add_of_le hle
      have hz := completed_suffix_zero hn ha (hkd ▸ hk)
      omega
    · obtain ⟨d,hnd⟩ := Nat.exists_eq_add_of_le hle
      have hz := completed_suffix_zero hk hb (hnd ▸ hn)
      omega
  subst k
  exact ⟨rfl,Prod.mk.inj (Except.ok.inj (hn.symm.trans hk))⟩

theorem successful_prefix {ctx oracle code n k s last events} (hle : k ≤ n)
    (hn : run ctx oracle code n s = .ok (last,events)) :
    ∃ mid headEvents, run ctx oracle code k s = .ok (mid,headEvents) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [run_add] at hn
  cases hk : run ctx oracle code k s with
  | error fault => simp [hk,Except.bind] at hn
  | ok result => exact ⟨result.1,result.2,rfl⟩

/-- A completed trace must extend any successfully produced running prefix.
This is a count comparison for two runs, not a termination assumption. -/
theorem completed_after_running_prefix {ctx oracle code n k s last mid events headEvents}
    (hn : run ctx oracle code n s = .ok (last,events)) (hd : last.scalar.core.thread.status = .done)
    (hk : run ctx oracle code k s = .ok (mid,headEvents)) (hr : mid.scalar.core.thread.status = .running) : k < n := by
  by_contra h
  obtain ⟨d,hkcount⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
  have hz := completed_suffix_zero hn hd (hkcount ▸ hk)
  have hk' : run ctx oracle code n s = .ok (mid,headEvents) := by
    simpa only [hkcount,hz,Nat.add_zero] using hk
  have hs : last = mid := (Prod.mk.inj (Except.ok.inj (hn.symm.trans hk'))).1
  rw [hs,hr] at hd
  cases hd

theorem step_after_running_prefix {ctx oracle code n k s last mid events headEvents}
    (hn : run ctx oracle code n s = .ok (last,events)) (hd : last.scalar.core.thread.status = .done)
    (hk : run ctx oracle code k s = .ok (mid,headEvents)) (hr : mid.scalar.core.thread.status = .running) :
    ∃ next emitted, step ctx oracle code mid = .ok (next,emitted) := by
  have hcount := completed_after_running_prefix hn hd hk hr
  obtain ⟨next,more,hmore⟩ := successful_prefix (by omega : k+1 ≤ n) hn
  rw [run_add,hk] at hmore
  simp only [Except.bind,run] at hmore
  cases hs : step ctx oracle code mid with
  | error fault => simp [hs] at hmore
  | ok result => exact ⟨result.1,result.2,rfl⟩

end
end Ptx.Ampere
