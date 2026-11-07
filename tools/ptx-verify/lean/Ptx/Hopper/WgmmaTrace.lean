import Ptx.Hopper.WgmmaRules

/-! Finite prefix/suffix reconstruction for the rich interpreter. Full states
and emitted events are preserved. A completed run cannot be extended by
padding fuel: stepping a done thread faults. No termination is asserted. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section

theorem run_done_suffix {ctx oracle code s} (hd : s.base.scalar.core.thread.status = .done) (n : Nat) :
    run ctx oracle code (n+1) s = .error .blocked := by
  simp [run,step,hd,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

theorem completed_suffix_zero {ctx oracle code k n s last events final allEvents}
    (hk : run ctx oracle code k s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done)
    (hn : run ctx oracle code (k+n) s = .ok (final,allEvents)) : n = 0 := by
  rw [run_add,hk] at hn
  simp only [Except.bind] at hn
  cases n with
  | zero => rfl
  | succ n => simp [run_done_suffix hd n] at hn

theorem complete_run_unique {ctx oracle code n k s a b ea eb}
    (hn : run ctx oracle code n s = .ok (a,ea)) (ha : a.base.scalar.core.thread.status = .done)
    (hk : run ctx oracle code k s = .ok (b,eb)) (hb : b.base.scalar.core.thread.status = .done) :
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

theorem completed_after_running_prefix {ctx oracle code n k s last mid events headEvents}
    (hn : run ctx oracle code n s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done)
    (hk : run ctx oracle code k s = .ok (mid,headEvents)) (hr : mid.base.scalar.core.thread.status = .running) : k < n := by
  by_contra h
  obtain ⟨d,hkcount⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
  have hz := completed_suffix_zero hn hd (hkcount ▸ hk)
  have hk' : run ctx oracle code n s = .ok (mid,headEvents) := by
    simpa only [hkcount,hz,Nat.add_zero] using hk
  have hs : last = mid := (Prod.mk.inj (Except.ok.inj (hn.symm.trans hk'))).1
  rw [hs,hr] at hd
  cases hd

theorem step_after_running_prefix {ctx oracle code n k s last mid events headEvents}
    (hn : run ctx oracle code n s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done)
    (hk : run ctx oracle code k s = .ok (mid,headEvents)) (hr : mid.base.scalar.core.thread.status = .running) :
    ∃ next emitted, step ctx oracle code mid = .ok (next,emitted) := by
  have hcount := completed_after_running_prefix hn hd hk hr
  obtain ⟨next,more,hmore⟩ := successful_prefix (by omega : k+1 ≤ n) hn
  rw [run_add,hk] at hmore
  simp only [Except.bind,run] at hmore
  cases hs : step ctx oracle code mid with
  | error fault => simp [hs] at hmore
  | ok result => exact ⟨result.1,result.2,rfl⟩

theorem run_suffix_of_prefix {ctx oracle code n k s last mid events headEvents}
    (hle : k ≤ n) (hn : run ctx oracle code n s = .ok (last,events))
    (hk : run ctx oracle code k s = .ok (mid,headEvents)) :
    ∃ tailEvents, run ctx oracle code (n-k) mid = .ok (last,tailEvents) ∧ events = headEvents++tailEvents := by
  have hn' : run ctx oracle code (k+(n-k)) s = .ok (last,events) := by simpa only [Nat.add_sub_of_le hle] using hn
  rw [run_add,hk] at hn'
  simp only [Except.bind] at hn'
  cases ht : run ctx oracle code (n-k) mid with
  | error fault => simp [ht] at hn'
  | ok result =>
    have he := Prod.mk.inj (Except.ok.inj (by simpa only [ht,Except.bind] using hn'))
    exact ⟨result.2,by rw [← he.1],he.2.symm⟩

end
end Ptx.Hopper.Wgmma
