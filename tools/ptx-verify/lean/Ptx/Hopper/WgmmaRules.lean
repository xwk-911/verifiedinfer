import Ptx.Hopper.WgmmaThread

/-! Source-local register/group guarantees. Collective memory/arithmetic and
ISA admission are deliberately not inferred from these protocol lemmas. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section

def Ledger.WellFormed (ledger : Ledger) : Prop := ledger.completed ≤ ledger.groups ∧ ∀ call ∈ ledger.calls, call.group ≤ ledger.groups

theorem initial_well_formed : Ledger.WellFormed {} := ⟨by decide,by simp⟩
theorem commit_well_formed {ledger : Ledger} (h : ledger.WellFormed) :
    Ledger.WellFormed {ledger with groups := ledger.groups+1,syncs := ledger.syncs+1} := by
  refine ⟨Nat.le_trans h.1 (Nat.le_succ _),?_⟩
  intro call hc
  exact Nat.le_trans (h.2 call hc) (Nat.le_succ _)
theorem issue_well_formed {ledger : Ledger} {call : Call}
    (h : ledger.WellFormed) (hg : call.group = ledger.groups) :
    Ledger.WellFormed {ledger with calls := ledger.calls++[call],syncs := ledger.syncs+1} := by
  refine ⟨h.1,?_⟩
  intro item hi
  simp only [List.mem_append,List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact h.2 item hi
  · exact Nat.le_of_eq hg
theorem completion_cut_monotone (ledger : Ledger) (keep reply) : ledger.completed ≤ completionCut ledger keep reply := Nat.le_max_left _ _
theorem completion_cut_required (ledger : Ledger) (keep reply) : ledger.groups-keep ≤ completionCut ledger keep reply :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
theorem completion_cut_bounded {ledger keep reply} (h : ledger.completed ≤ ledger.groups) : completionCut ledger keep reply ≤ ledger.groups := by
  unfold completionCut
  exact max_le h (max_le (Nat.sub_le _ _) (min_le_left _ _))
theorem wait_zero_completes_committed {ledger reply} (h : ledger.completed ≤ ledger.groups) : completionCut ledger 0 reply = ledger.groups := by
  have hb := completion_cut_bounded (keep := 0) (reply := reply) h
  have hl := completion_cut_required ledger 0 reply
  omega
theorem wait_preserves_groups (s : State) (keep reply) : (waitState s keep reply).ledger.groups = s.ledger.groups := rfl
theorem wait_preserves_calls (s : State) (keep reply) : (waitState s keep reply).ledger.calls = s.ledger.calls := rfl
theorem wait_well_formed {s keep reply} (h : Ledger.WellFormed s.ledger) : Ledger.WellFormed (waitState s keep reply).ledger :=
  ⟨completion_cut_bounded h.1,h.2⟩

theorem uncommitted_stays_pending {ledger call} (hw : Ledger.WellFormed ledger)
    (hc : call ∈ ledger.calls) (hg : call.group = ledger.groups) (keep reply) :
    call ∈ pending {ledger with completed := completionCut ledger keep reply} := by
  apply List.mem_filter.mpr
  exact ⟨hc,by simpa [hg] using completion_cut_bounded (keep := keep) (reply := reply) hw.1⟩

theorem completed_cut_never_reopens {ledger : Ledger} {call : Call} {keep reply : Nat}
    (hc : call.group < ledger.completed) : call ∉ pending {ledger with completed := completionCut ledger keep reply} := by
  intro hm
  have hh := (List.mem_filter.mp hm).2
  have hm := completion_cut_monotone ledger keep reply
  simp only [decide_eq_true_eq] at hh
  omega

theorem write_result_pc (s : Hopper.State) (call : Call) : (writeResult s call).scalar.core.thread.pc = s.scalar.core.thread.pc := rfl
theorem write_result_queries (s : Hopper.State) (call : Call) : (writeResult s call).scalar.core.queries = s.scalar.core.queries := rfl
theorem write_result_mma_counter (s : Hopper.State) (call : Call) : (writeResult s call).mmaCalls = s.mmaCalls := rfl

theorem complete_of_metadata (s : State)
    (h : ((s.base.scalar.core.thread.status == .done) && ((pending s.ledger).length == 0)) = true) : Complete s := by
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  exact ⟨h.1,List.eq_nil_of_length_eq_zero h.2⟩

theorem ordinary_step {ctx oracle code s instruction after events}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some instruction)
    (hn : ∀ wg, instruction ≠ .wgmma wg)
    (hp : (ordinaryNames instruction).find? (fun name => (pendingNames s.ledger).contains name) = none)
    (hb : Hopper.step ctx oracle.base code s.base = .ok (after,events)) :
    step ctx oracle code s = .ok ({base := after,ledger := {s.ledger with dirty := (ordinaryNames instruction++s.ledger.dirty).eraseDups}},events.map Event.base) := by
  simp only [List.contains_eq_mem] at hp
  cases instruction <;> try exact (hn _ rfl).elim
  all_goals simp [step,hr,hi,hp,hb,liftBase,bind,Except.bind,pure,Except.pure]

theorem ordinary_pending_fault {ctx oracle code s instruction name}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some instruction)
    (hn : ∀ wg, instruction ≠ .wgmma wg)
    (hp : (ordinaryNames instruction).find? (fun r => (pendingNames s.ledger).contains r) = some name) :
    step ctx oracle code s = .error (.pendingRegister name) := by
  simp only [List.contains_eq_mem] at hp
  cases instruction <;> try exact (hn _ rfl).elim
  all_goals (simp [step,hr,hi,hp,bind,Except.bind,pure,Except.pure]; rfl)

theorem missing_register_fence_fault {ctx oracle code s d a b scaleD}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.wgmma (.mma d a b scaleD)))
    (hf : s.ledger.fenced = false) : step ctx oracle code s = .error .needsFence := by
  simp [step,hr,hi,hf,bind,Except.bind]; rfl

theorem invalid_wait_fault {ctx oracle code s keep}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.wgmma (.wait keep)))
    (hk : 8 ≤ keep) : step ctx oracle code s = .error (.waitCount keep) := by
  simp [step,hr,hi,hk,bind,Except.bind]; rfl

theorem fence_does_not_complete {ctx oracle code s}
    (hr : s.base.scalar.core.thread.status = .running) (hi : code[s.base.scalar.core.thread.pc]? = some (.wgmma .fence)) :
    step ctx oracle code s = .ok ({base := Ampere.advance s.base,ledger := {s.ledger with fenced := true,dirty := [],syncs := s.ledger.syncs+1}},[.fence (mark ctx s)]) := by
  simp [step,hr,hi,bind,Except.bind,pure,Except.pure]

theorem commit_creates_distinct_group {ctx oracle code s}
    (hr : s.base.scalar.core.thread.status = .running) (hi : code[s.base.scalar.core.thread.pc]? = some (.wgmma .commit)) :
    step ctx oracle code s = .ok ({base := Ampere.advance s.base,ledger := {s.ledger with groups := s.ledger.groups+1,syncs := s.ledger.syncs+1}},[.commit (mark ctx s) s.ledger.groups]) := by
  simp [step,hr,hi,bind,Except.bind,pure,Except.pure]

theorem run_eq_plain (ctx : Scalar.Context) (oracle : Oracle) (code : List Hopper.Instr) (n : Nat) (s : State) :
    run ctx oracle code n s = SourceRun.plain (step ctx oracle code) n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [run,SourceRun.plain,ih]

theorem run_add (ctx : Scalar.Context) (oracle : Oracle) (code : List Hopper.Instr)
    (n m : Nat) (s : State) :
    run ctx oracle code (n+m) s = (run ctx oracle code n s).bind (fun first =>
      (run ctx oracle code m first.1).bind (fun last => .ok (last.1,first.2++last.2))) := by
  induction n generalizing s with
  | zero => cases hr : run ctx oracle code m s <;> simp [run,hr,Except.bind]
  | succ n ih =>
    cases hs : step ctx oracle code s with
    | error fault => simp [Nat.succ_add,run,hs,Except.bind]
    | ok first =>
      rcases first with ⟨mid,head⟩
      rw [Nat.succ_add,run,hs]
      simp only [Except.bind]
      rw [ih]
      cases hr : run ctx oracle code n mid with
      | error fault => simp [run,hs,hr,Except.bind]
      | ok result =>
        rcases result with ⟨next,rest⟩
        simp only [hr,Except.bind]
        cases ht : run ctx oracle code m next <;> simp [run,hs,hr,ht,Except.bind,List.append_assoc]

theorem run_located_exists {ctx oracle code n s last events}
    (h : run ctx oracle code n s = .ok (last,events)) :
    ∃ located, runLocated ctx oracle code n s = .ok (last,located) ∧ located.map SourceRun.Located.kind = events := by
  rw [run_eq_plain] at h
  exact SourceRun.of_plain h
theorem run_located_erases {ctx oracle code n s last located}
    (h : runLocated ctx oracle code n s = .ok (last,located)) :
    run ctx oracle code n s = .ok (last,located.map SourceRun.Located.kind) := by
  rw [run_eq_plain]
  exact SourceRun.erases h

theorem run_located_erases_result {ctx oracle code n s} {value : State × List (SourceRun.Located Event)}
    (h : runLocated ctx oracle code n s = .ok value) :
    run ctx oracle code n s = .ok (value.1,value.2.map SourceRun.Located.kind) := by
  rcases value with ⟨last,located⟩
  exact run_located_erases h

end
end Ptx.Hopper.Wgmma
