import Ptx.Ordered.Thread
import Ptx.Scalar.Execution

/-! Generic finite-run decomposition. A completed execution of a loop with
fixed-size local chunks consists of finitely many loop chunks and an exit
chunk. This neither bounds polling iterations nor proves termination. -/
namespace Ptx.Ordered
noncomputable section

theorem run_add (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) (n m : Nat) (state : State) :
    run ctx oracle code (n+m) state = (run ctx oracle code n state).bind (fun first =>
      (run ctx oracle code m first.1).bind (fun last => .ok (last.1,first.2++last.2))) := by
  induction n generalizing state with
  | zero => cases hr : run ctx oracle code m state <;> simp [run,hr,Except.bind]
  | succ n ih =>
    cases hs : step ctx oracle code state with
    | error fault => simp [Nat.succ_add,run,hs,Except.bind]
    | ok first =>
      obtain ⟨mid,events⟩ := first
      rw [Nat.succ_add,run,hs]
      simp only [Except.bind]
      rw [ih]
      cases hr : run ctx oracle code n mid with
      | error fault => simp [run,hs,hr,Except.bind]
      | ok result =>
        obtain ⟨next,rest⟩ := result
        simp [run,hs,hr,Except.bind]
        cases run ctx oracle code m next <;> rfl

theorem successful_prefix {ctx oracle code n k state last events} (hle : k ≤ n)
    (hn : run ctx oracle code n state = .ok (last,events)) :
    ∃ mid headEvents, run ctx oracle code k state = .ok (mid,headEvents) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [run_add] at hn
  cases hk : run ctx oracle code k state with
  | error fault => simp [hk,Except.bind] at hn
  | ok result => exact ⟨result.1,result.2,rfl⟩

theorem successful_first_step {ctx oracle code n state last events}
    (hr : run ctx oracle code (n+1) state = .ok (last,events)) :
    ∃ next first, step ctx oracle code state = .ok (next,first) := by
  cases hs : step ctx oracle code state with
  | error fault => simp [run,hs,Except.bind] at hr
  | ok result => exact ⟨result.1,result.2,rfl⟩

theorem successful_suffix {ctx oracle code n k state mid last headEvents events} (hle : k ≤ n)
    (hk : run ctx oracle code k state = .ok (mid,headEvents))
    (hn : run ctx oracle code n state = .ok (last,events)) :
    ∃ remaining tailEvents, n = k+remaining ∧ run ctx oracle code remaining mid = .ok (last,tailEvents) ∧
      events = headEvents++tailEvents := by
  obtain ⟨remaining,he⟩ := Nat.exists_eq_add_of_le hle
  have h := hn
  rw [he,run_add,hk] at h
  simp only [Except.bind] at h
  cases ht : run ctx oracle code remaining mid with
  | error fault => simp [ht] at h
  | ok result =>
    obtain ⟨final,tailEvents⟩ := result
    simp only [ht,Except.ok.injEq,Prod.mk.injEq] at h
    exact ⟨remaining,tailEvents,he,h.1 ▸ ht,h.2.symm⟩

theorem complete_run_unique {ctx oracle code n k state a b ea eb}
    (hn : run ctx oracle code n state = .ok (a,ea)) (ha : a.core.thread.status = .done)
    (hk : run ctx oracle code k state = .ok (b,eb)) (hb : b.core.thread.status = .done) :
    n = k ∧ a = b ∧ ea = eb := by
  have hcount := (Scalar.complete_run_unique (run_preserves_scalar_events hn) ha (run_preserves_scalar_events hk) hb).1
  subst k
  exact ⟨rfl,Prod.mk.inj (Except.ok.inj (hn.symm.trans hk))⟩

theorem completed_after_running_prefix {ctx oracle code n k state last mid events first}
    (hn : run ctx oracle code n state = .ok (last,events)) (hd : last.core.thread.status = .done)
    (hk : run ctx oracle code k state = .ok (mid,first)) (hr : mid.core.thread.status = .running) : k < n :=
  Scalar.completed_after_running_prefix (run_preserves_scalar_events hn) hd (run_preserves_scalar_events hk) hr

inductive LoopChunks (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr)
    (width : Nat) (keep exit : State → Prop) : State → List Kind → State → Prop
  | stop {state} : exit state → LoopChunks ctx oracle code width keep exit state [] state
  | next {state mid last first rest} : keep state → run ctx oracle code width state = .ok (mid,first) →
      LoopChunks ctx oracle code width keep exit mid rest last →
      LoopChunks ctx oracle code width keep exit state (first++rest) last

theorem completed_loop_decomposition {ctx oracle code width keep exit}
    (hw : 0 < width)
    (keep_running : ∀ state, keep state → ∀ count, count < width → ∀ last events,
      run ctx oracle code count state = .ok (last,events) → last.core.thread.status = .running)
    (keep_step : ∀ state, keep state → ∀ next events,
      run ctx oracle code width state = .ok (next,events) → keep next ∨ exit next)
    (exit_running : ∀ state, exit state → ∀ count, count < width → ∀ last events,
      run ctx oracle code count state = .ok (last,events) → last.core.thread.status = .running)
    (exit_done : ∀ state, exit state → ∀ last events,
      run ctx oracle code width state = .ok (last,events) → last.core.thread.status = .done)
    {count state last events} (hs : keep state) (hr : run ctx oracle code count state = .ok (last,events))
    (hd : last.core.thread.status = .done) :
    ∃ leaving first tail, LoopChunks ctx oracle code width keep exit state first leaving ∧ exit leaving ∧
      run ctx oracle code width leaving = .ok (last,tail) ∧ events = first++tail := by
  induction count using Nat.strong_induction_on generalizing state last events with
  | h count ih =>
    have hwidth : width ≤ count := by
      by_contra hn
      have hrun := keep_running state hs count (by omega) last events hr
      rw [hd] at hrun
      cases hrun
    obtain ⟨mid,head,hhead⟩ := successful_prefix hwidth hr
    obtain ⟨remaining,rest,hcount,hrest,hevents⟩ := successful_suffix hwidth hhead hr
    rcases keep_step state hs mid head hhead with hkeep | hexit
    · obtain ⟨leaving,first,tail,hchunks,hleaving,htail,hend⟩ := ih remaining (by omega) hkeep hrest hd
      exact ⟨leaving,head++first,tail,.next hs hhead hchunks,hleaving,htail,
        by rw [hevents,hend,List.append_assoc]⟩
    · have htailwidth : width ≤ remaining := by
        by_contra hn
        have hrun := exit_running mid hexit remaining (by omega) last rest hrest
        rw [hd] at hrun
        cases hrun
      obtain ⟨final,tail,htail⟩ := successful_prefix htailwidth hrest
      have heq := (complete_run_unique hrest hd htail (exit_done mid hexit final tail htail)).1
      exact ⟨mid,head,rest,by simpa only [List.append_nil] using (LoopChunks.next hs hhead (.stop hexit)),
        hexit,by simpa only [heq] using hrest,hevents⟩

end
end Ptx.Ordered
