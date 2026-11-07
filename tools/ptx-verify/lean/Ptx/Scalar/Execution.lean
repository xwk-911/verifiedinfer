import Ptx.Scalar.Thread
import Ptx.Event.Contracts

/-! Launch-wide candidates for the mixed scalar interpreter. The shared graph
stores the actual scalar oracle, event list and final integer/control state.
Provenance additionally reconstructs the complete float register bank; it is
never delegated to the integer interpreter or an erased float program.
The memory and observer predicates are the SAME polymorphic definitions used by
integer candidates. This does not establish their full PTX correspondence.
-/
namespace Ptx.Scalar
open Ptx.ISA
noncomputable section

abbrev ThreadTrace := Event.ThreadTrace Symbolic.Byte Oracle
abbrev Candidate := Event.Candidate Symbolic.Byte Oracle
abbrev Launch := Event.Launch Symbolic.Byte
abbrev ByteMap := Event.ByteMap Symbolic.Byte
abbrev Observation := Event.Observation Symbolic.Byte

theorem run_append {ctx oracle code n m s mid last headEvents tailEvents}
    (hn : run ctx oracle code n s = .ok (mid,headEvents))
    (hm : run ctx oracle code m mid = .ok (last,tailEvents)) :
    run ctx oracle code (n+m) s = .ok (last,headEvents ++ tailEvents) := by
  rw [run_add,hn]
  simp only [Except.bind,hm]

theorem successful_suffix {ctx oracle code n k s mid last headEvents events}
    (hle : k ≤ n) (hk : run ctx oracle code k s = .ok (mid,headEvents))
    (hn : run ctx oracle code n s = .ok (last,events)) :
    ∃ remaining tailEvents, n = k+remaining ∧
      run ctx oracle code remaining mid = .ok (last,tailEvents) ∧ events = headEvents ++ tailEvents := by
  obtain ⟨remaining,he⟩ := Nat.exists_eq_add_of_le hle
  have h := hn
  rw [he,run_add,hk] at h
  simp only [Except.bind] at h
  cases ht : run ctx oracle code remaining mid with
  | error fault => simp [ht] at h
  | ok result =>
    rcases result with ⟨final,tailEvents⟩
    simp only [ht,Except.ok.injEq,Prod.mk.injEq] at h
    exact ⟨remaining,tailEvents,he,h.1 ▸ ht,h.2.symm⟩

def Produced (code : List Instr) (params : Bindings) (t : ThreadTrace) (block : Dim3 := .one) : Prop :=
  ∃ floats, run {id := t.id,params := params,block := block} t.oracle code t.count {} = .ok (⟨t.final,floats⟩,t.events)

def WellFormed (code : List Instr) (launch : Launch) (c : Candidate) : Prop :=
  launch.geometry.Valid ∧
  (c.traces.map Event.ThreadTrace.id).Nodup ∧
  (∀ t ∈ c.traces, t.id.Valid launch.geometry ∧ Produced code launch.params t launch.geometry.block) ∧
  (∀ id, id.Valid launch.geometry → ∃ t ∈ c.traces, t.id = id)

theorem produced_runs {code params t block} (h : Produced code params t block) :
    ∃ floats, Runs {id := t.id,params := params,block := block} t.oracle code {} t.events ⟨t.final,floats⟩ := by
  obtain ⟨floats,h⟩ := h
  exact ⟨floats,run_sound h⟩

theorem candidate_trace_runs {code launch c t} (hw : WellFormed code launch c)
    (ht : t ∈ c.traces) :
    ∃ floats, Runs {id := t.id,params := launch.params,block := launch.geometry.block} t.oracle code {} t.events ⟨t.final,floats⟩ :=
  produced_runs (hw.2.2.1 t ht).2

def Triple (code : List Instr) (pre : Launch → Prop) (domain : Launch → List Location)
    (post : Launch → ByteMap → Prop) : Prop :=
  ∀ launch c rf co o, pre launch → WellFormed code launch c →
    Event.GenericMemoryConditions c launch.initial rf co →
    Event.ObserverConditions c launch.initial rf co o → o.domain = domain launch → post launch o.output

def Nonvacuous (code : List Instr) (pre : Launch → Prop) (domain : Launch → List Location) : Prop :=
  ∀ launch, pre launch → ∃ c rf co o, WellFormed code launch c ∧
    Event.GenericMemoryConditions c launch.initial rf co ∧
    Event.ObserverConditions c launch.initial rf co o ∧ o.domain = domain launch

theorem triple_apply {code pre domain post launch c rf co o}
    (hc : Triple code pre domain post) (hp : pre launch) (hw : WellFormed code launch c)
    (hm : Event.GenericMemoryConditions c launch.initial rf co)
    (ho : Event.ObserverConditions c launch.initial rf co o) (hd : o.domain = domain launch) :
    post launch o.output := hc launch c rf co o hp hw hm ho hd

theorem run_done_suffix {ctx oracle code s} (hd : s.core.thread.status = .done) (n : Nat) :
    run ctx oracle code (n+1) s = .error (.integer .blocked) := by
  simp [run,run_after_done hd,Except.bind]

theorem completed_suffix_zero {ctx oracle code k n s last events final allEvents}
    (hk : run ctx oracle code k s = .ok (last,events)) (hd : last.core.thread.status = .done)
    (hn : run ctx oracle code (k+n) s = .ok (final,allEvents)) : n = 0 := by
  rw [run_add,hk] at hn
  simp only [Except.bind] at hn
  cases n with
  | zero => rfl
  | succ n => simp [run_done_suffix hd n] at hn

theorem complete_run_unique {ctx oracle code n k s a b ea eb}
    (hn : run ctx oracle code n s = .ok (a,ea)) (ha : a.core.thread.status = .done)
    (hk : run ctx oracle code k s = .ok (b,eb)) (hb : b.core.thread.status = .done) :
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
    (hn : run ctx oracle code n s = .ok (last,events)) (hd : last.core.thread.status = .done)
    (hk : run ctx oracle code k s = .ok (mid,headEvents)) (hr : mid.core.thread.status = .running) : k < n := by
  by_contra h
  obtain ⟨d,hkcount⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
  have hz := completed_suffix_zero hn hd (hkcount ▸ hk)
  have hk' : run ctx oracle code n s = .ok (mid,headEvents) := by
    simpa only [hkcount,hz,Nat.add_zero] using hk
  have hs : last = mid := (Prod.mk.inj (Except.ok.inj (hn.symm.trans hk'))).1
  rw [hs,hr] at hd
  cases hd

theorem step_after_running_prefix {ctx oracle code n k s last mid events headEvents}
    (hn : run ctx oracle code n s = .ok (last,events)) (hd : last.core.thread.status = .done)
    (hk : run ctx oracle code k s = .ok (mid,headEvents)) (hr : mid.core.thread.status = .running) :
    ∃ next emitted, step ctx oracle code mid = .ok (next,emitted) := by
  have hcount := completed_after_running_prefix hn hd hk hr
  obtain ⟨next,more,hmore⟩ := successful_prefix (by omega : k+1 ≤ n) hn
  rw [run_add,hk] at hmore
  simp only [Except.bind,run] at hmore
  cases hs : step ctx oracle code mid with
  | error fault => simp [hs] at hmore
  | ok result => exact ⟨result.1,result.2,rfl⟩

end
end Ptx.Scalar
