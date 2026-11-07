import Ptx.Event.Thread

/-! Interpreter-independent source-location instrumentation. The PC is read from
the actual pre-step state for every emitted event. Erasure exactly preserves
the original finite execution; source annotations are not oracle-supplied data. -/
namespace Ptx.SourceRun

structure Located (Kind : Type) where
  kind : Kind
  pc : Nat
  deriving Repr, DecidableEq

variable {State Fault Kind : Type}

def plain (step : State → Except Fault (State × List Kind)) :
    Nat → State → Except Fault (State × List Kind)
  | 0,s => .ok (s,[])
  | n+1,s => (step s).bind fun first =>
      (plain step n first.1).bind fun last => .ok (last.1,first.2 ++ last.2)

def run (step : State → Except Fault (State × List Kind)) (pc : State → Nat) :
    Nat → State → Except Fault (State × List (Located Kind))
  | 0,s => .ok (s,[])
  | n+1,s => (step s).bind fun first =>
      (run step pc n first.1).bind fun last =>
        .ok (last.1,first.2.map (fun kind => ⟨kind,pc s⟩) ++ last.2)

theorem run_add (step : State → Except Fault (State × List Kind)) (pc : State → Nat)
    (n m : Nat) (s : State) : run step pc (n+m) s = (run step pc n s).bind (fun first =>
      (run step pc m first.1).bind (fun last => .ok (last.1,first.2++last.2))) := by
  induction n generalizing s with
  | zero => cases hr : run step pc m s <;> simp [run,hr,Except.bind]
  | succ n ih =>
    cases hs : step s with
    | error fault => simp [Nat.succ_add,run,hs,Except.bind]
    | ok first =>
      rcases first with ⟨mid,head⟩
      rw [Nat.succ_add,run,hs]
      simp only [Except.bind]
      rw [ih]
      cases hr : run step pc n mid with
      | error fault => simp [run,hs,hr,Except.bind]
      | ok result =>
        rcases result with ⟨next,rest⟩
        simp [run,hs,hr,Except.bind]
        cases run step pc m next <;> simp

theorem of_plain {step : State → Except Fault (State × List Kind)} {pc : State → Nat}
    {n : Nat} {s last : State} {events : List Kind} (h : plain step n s = .ok (last,events)) :
    ∃ located, run step pc n s = .ok (last,located) ∧ located.map Located.kind = events := by
  induction n generalizing s last events with
  | zero =>
    simp only [plain,Except.ok.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact ⟨[],rfl,rfl⟩
  | succ n ih =>
    cases hs : step s with
    | error fault => simp [plain,hs,Except.bind] at h
    | ok first =>
      rcases first with ⟨mid,head⟩
      cases ht : plain step n mid with
      | error fault => simp [plain,hs,ht,Except.bind] at h
      | ok tail =>
        rcases tail with ⟨final,rest⟩
        simp only [plain,hs,ht,Except.bind,Except.ok.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        obtain ⟨located,hl,he⟩ := ih ht
        refine ⟨head.map (fun kind => ⟨kind,pc s⟩) ++ located,?_,?_⟩
        · simp only [run,hs,hl,Except.bind]
        · simp only [List.map_append,List.map_map,Function.comp_def,he]
          simp

theorem erases {step : State → Except Fault (State × List Kind)} {pc : State → Nat}
    {n : Nat} {s last : State} {events : List (Located Kind)} (h : run step pc n s = .ok (last,events)) :
    plain step n s = .ok (last,events.map Located.kind) := by
  induction n generalizing s last events with
  | zero =>
    simp only [run,Except.ok.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    rfl
  | succ n ih =>
    cases hs : step s with
    | error fault => simp [run,hs,Except.bind] at h
    | ok first =>
      rcases first with ⟨mid,head⟩
      cases ht : run step pc n mid with
      | error fault => simp [run,hs,ht,Except.bind] at h
      | ok tail =>
        rcases tail with ⟨final,rest⟩
        simp only [run,hs,ht,Except.bind,Except.ok.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        simp only [plain,hs,ih ht,Except.bind,List.map_append,List.map_map,Function.comp_def]
        simp

/-- Locate an actual emitted event after a proven plain prefix. The annotation
comes from the pre-step state; no complete annotated trace must be replayed. -/
theorem at_boundary {step : State → Except Fault (State × List Kind)} {pc : State → Nat}
    {k n : Nat} {s before after last : State} {head emitted : List Kind} {located : List (Located Kind)}
    (hp : plain step k s = .ok (before,head)) (hs : step before = .ok (after,emitted))
    (ht : run step pc (k+(n+1)) s = .ok (last,located)) {offset : Nat} {kind : Kind}
    (he : emitted[offset]? = some kind) : located[head.length+offset]? = some ⟨kind,pc before⟩ := by
  obtain ⟨prefixLocated,hp',herase⟩ := of_plain (pc := pc) hp
  have hlen : prefixLocated.length = head.length := by rw [← herase,List.length_map]
  rw [run_add,hp'] at ht
  simp only [Except.bind] at ht
  rw [run,hs] at ht
  simp only [Except.bind] at ht
  cases htail : run step pc n after with
  | error fault => simp [htail] at ht
  | ok result =>
    rcases result with ⟨final,rest⟩
    have hloc : located = prefixLocated++(emitted.map (fun e => ⟨e,pc before⟩)++rest) := by
      simp only [htail,Except.bind,Except.ok.injEq,Prod.mk.injEq] at ht
      exact ht.2.symm
    rw [hloc,List.getElem?_append_right (by omega),hlen,Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left (by simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp he).1),List.getElem?_map,he]
    rfl

theorem event_origin {step : State → Except Fault (State × List Kind)} {pc : State → Nat}
    {n : Nat} {s last : State} {events : List (Located Kind)}
    (h : run step pc n s = .ok (last,events)) {serial : Nat} {event : Located Kind}
    (he : events[serial]? = some event) :
    ∃ before after emitted, step before = .ok (after,emitted) ∧ event.kind ∈ emitted ∧ event.pc = pc before := by
  induction n generalizing s last events serial with
  | zero => simp [run] at h; rcases h with ⟨rfl,rfl⟩; simp at he
  | succ n ih =>
    cases hs : step s with
    | error fault => simp [run,hs,Except.bind] at h
    | ok first =>
      rcases first with ⟨mid,head⟩
      cases ht : run step pc n mid with
      | error fault => simp [run,hs,ht,Except.bind] at h
      | ok tail =>
        rcases tail with ⟨final,rest⟩
        simp only [run,hs,ht,Except.bind,Except.ok.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        by_cases hb : serial < head.length
        · rw [List.getElem?_append_left (by simpa using hb)] at he
          obtain ⟨kind,hk,heq⟩ := List.mem_map.mp (List.mem_of_getElem? he)
          subst event
          exact ⟨s,mid,head,hs,hk,rfl⟩
        · rw [List.getElem?_append_right (by simp; omega)] at he
          exact ih ht he

end Ptx.SourceRun
