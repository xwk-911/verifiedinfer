import Ptx.Shuffle.Thread

/-! Exact completion counts for the source interpreter. A completed run cannot
be extended by extra successful source steps, regardless of oracle answers. -/
namespace Ptx.Shuffle
open Ptx.ISA
noncomputable section

theorem run_join {ctx oracle code n m state mid final head tail}
    (hn : run ctx oracle code n state = .ok (mid,head))
    (hm : run ctx oracle code m mid = .ok (final,tail)) :
    run ctx oracle code (n+m) state = .ok (final,head++tail) := by
  rw [run_add,hn]
  simp only [Except.bind,hm,Except.map]

theorem step_after_done {ctx oracle code state} (hd : state.base.core.thread.status = .done) :
    step ctx oracle code state = .error (.integer .blocked) := by
  simp [step,hd,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

theorem run_done_suffix {ctx oracle code state} (hd : state.base.core.thread.status = .done) (n : Nat) :
    run ctx oracle code (n+1) state = .error (.integer .blocked) := by
  simp [run,step_after_done hd,Except.bind]

theorem completed_suffix_zero {ctx oracle code k n state last events final allEvents}
    (hk : run ctx oracle code k state = .ok (last,events)) (hd : last.base.core.thread.status = .done)
    (hn : run ctx oracle code (k+n) state = .ok (final,allEvents)) : n = 0 := by
  rw [run_add,hk] at hn
  simp only [Except.bind] at hn
  cases n with
  | zero => rfl
  | succ n => simp [run_done_suffix hd n,Except.map] at hn

theorem complete_run_unique {ctx oracle code n k state a b ea eb}
    (hn : run ctx oracle code n state = .ok (a,ea)) (ha : a.base.core.thread.status = .done)
    (hk : run ctx oracle code k state = .ok (b,eb)) (hb : b.base.core.thread.status = .done) :
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

end
end Ptx.Shuffle
