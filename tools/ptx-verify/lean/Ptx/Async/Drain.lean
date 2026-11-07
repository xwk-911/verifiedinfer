import Ptx.Async.Preparation
import Ptx.Async.LoanPreservation
import Ptx.Async.Clients

/-! Construct finite FIFO drain/acquire executions in the real protocol.
The queue must contain no event waits; this is checked for the prepared request
language. This proves existence, not scheduler fairness or runtime termination.
-/
namespace Ptx.Async.Drain

def metadata (s : State) : List (Bool × List Loan) := s.buffers.map (fun buffer => (buffer.alive,buffer.loans))
def Plain (commands : List Command) : Prop := ∀ command ∈ commands, ∀ ticket, command ≠ .wait ticket
def Returned (s : State) : Prop := ∀ (bid : Nat) (buffer : Buffer), s.buffers[bid]? = some buffer → buffer.loans = []
def clearLoans (s : State) : State := {s with buffers := s.buffers.map (fun buffer => {buffer with loans := []})}

theorem value_update_metadata {s bid buffer value} (hg : s.buffers[bid]? = some buffer) :
    metadata {s with buffers := s.buffers.set bid {buffer with value := value}} = metadata s := by
  apply List.ext_getElem?
  intro other
  have hlt := (List.getElem?_eq_some_iff.mp hg).1
  by_cases he : other = bid
  · subst other
    simp only [metadata,List.getElem?_map,List.getElem?_set_self hlt,hg,Option.map_some]
  · simp only [metadata,List.getElem?_map,List.getElem?_set_ne (Ne.symm he)]

theorem execute_resources {s command next} (hs : execute s command = .ok next) :
    next.events = s.events ∧ metadata next = metadata s := by
  cases command with
  | wait ticket =>
    cases hc : complete s ticket <;> simp [execute,hc,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at hs
    subst next; exact ⟨rfl,rfl⟩
  | use bid =>
    cases hg : getBuffer s bid with
    | error e => simp [execute,hg,bind,Except.bind] at hs
    | ok buffer =>
      simp [execute,hg,bind,Except.bind,pure,Except.pure] at hs
      subst next; exact ⟨rfl,rfl⟩
  | access bid mode =>
    cases hg : getBuffer s bid with
    | error e => simp [execute,hg,bind,Except.bind] at hs
    | ok buffer =>
      simp [execute,hg,bind,Except.bind,pure,Except.pure] at hs
      subst next; exact ⟨rfl,rfl⟩
  | copy src dst =>
    cases ha : getBuffer s src with
    | error e => simp [execute,ha,bind,Except.bind] at hs
    | ok a =>
      cases hb : getBuffer s dst with
      | error e => simp [execute,ha,hb,bind,Except.bind] at hs
      | ok b =>
        simp [execute,ha,hb,bind,Except.bind,pure,Except.pure] at hs
        subst next
        exact ⟨rfl,value_update_metadata (getBuffer_iff.mp hb).1⟩

theorem device_resources {s sid next} (hs : deviceStep s sid = .ok next) :
    next.events = s.events ∧ metadata next = metadata s := by
  unfold deviceStep at hs
  cases hg : getStream s sid with
  | error e => simp [hg,bind,Except.bind] at hs
  | ok stream =>
    cases hh : stream.queue.head? with
    | none => simp [hg,hh,bind,Except.bind] at hs
    | some command =>
      cases he : execute s command with
      | error e => simp [hg,hh,he,bind,Except.bind] at hs
      | ok mid =>
        simp [hg,hh,he,bind,Except.bind,pure,Except.pure] at hs
        subst next
        simpa only [metadata] using (execute_resources (next := mid) he)

theorem metadata_lookup {before after} {bid : Nat} {actual : Buffer} (hm : metadata after = metadata before)
    (ha : after.buffers[bid]? = some actual) :
    ∃ old : Buffer, before.buffers[bid]? = some old ∧ actual.alive = old.alive ∧ actual.loans = old.loans := by
  have he := congrArg (fun entries => entries[bid]?) hm
  cases hb : before.buffers[bid]? with
  | none => simp [metadata,List.getElem?_map,ha,hb] at he
  | some old =>
    refine ⟨old,rfl,?_⟩
    simpa [metadata,List.getElem?_map,ha,hb] using he

theorem metadata_live {before after} (hm : metadata after = metadata before) (hl : Preparation.Live before) : Preparation.Live after := by
  intro bid actual ha
  obtain ⟨old,hg,he,_⟩ := metadata_lookup hm ha
  exact he.trans (hl bid old hg)

theorem metadata_bounded {before after limit} (hm : metadata after = metadata before) (hb : Preparation.Bounded before limit) :
    Preparation.Bounded after limit := by
  intro bid actual ha loan hl
  obtain ⟨old,hg,_,he⟩ := metadata_lookup hm ha
  exact hb bid old hg loan (he ▸ hl)

theorem metadata_length {before after} (hm : metadata after = metadata before) : after.buffers.length = before.buffers.length := by
  simpa [metadata] using congrArg List.length hm

theorem requests_plain (requests : List Preparation.Request) : Plain (requests.map Preparation.Request.command) := by
  intro command hm ticket he
  obtain ⟨request,_,rfl⟩ := List.mem_map.mp hm
  cases request <;> cases he

theorem drain_queue (s : State) (issued completed : Nat) (commands : List Command) (dependencies : List Ticket)
    (hshape : s.streams = [⟨issued,completed,commands,dependencies⟩]) (hi : Invariant s) (hp : Plain commands) :
    ∃ final, run s (List.replicate commands.length (.device 0)) = .ok final ∧
      final.streams = [⟨issued,completed+commands.length,[],dependencies⟩] ∧ final.events = s.events ∧ metadata final = metadata s := by
  induction commands generalizing s completed with
  | nil => exact ⟨s,rfl,by simpa using hshape,rfl,rfl⟩
  | cons command rest ih =>
    have hg : s.streams[0]? = some ⟨issued,completed,command::rest,dependencies⟩ := by rw [hshape]; rfl
    obtain ⟨mid,hs⟩ := deviceStep_ready hi hg rfl (by intro ticket he; exact (hp command (by simp) ticket he).elim)
    obtain ⟨stream,hstream,hnext⟩ := deviceStep_streams hs
    have heq : stream = ⟨issued,completed,command::rest,dependencies⟩ := by simpa only [hg,Option.some.injEq] using (getStream_iff.mp hstream).symm
    subst stream
    have hmid : mid.streams = [⟨issued,completed+1,rest,dependencies⟩] := by rw [hnext,hshape]; rfl
    obtain ⟨final,hr,hfinal,he,hm⟩ := ih mid (completed+1) hmid (deviceStep_invariant hi hs)
      (by intro actual ha ticket; exact hp actual (by simp [ha]) ticket)
    refine ⟨final,by simpa [List.length_cons,List.replicate_succ,run,step,hs,Except.bind] using hr,?_,
      he.trans (device_resources hs).1,hm.trans (device_resources hs).2⟩
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hfinal

theorem await_all_loans {s event total} (he : getEvent s event = .ok ⟨0,total⟩)
    (hc : complete s ⟨0,total⟩ = true) (hb : Preparation.Bounded s total) : await s event = .ok (clearLoans s) := by
  have hfilter : ∀ (bid : Nat) (buffer : Buffer), s.buffers[bid]? = some buffer →
      buffer.loans.filter (fun loan => !covers ⟨0,total⟩ loan.ticket) = [] := by
    intro bid buffer hg
    apply List.filter_eq_nil_iff.mpr
    intro loan hl
    have h := hb bid buffer hg loan hl
    simp [covers,h.1,h.2]
  have hbuffers : s.buffers.map (fun buffer => {buffer with loans := buffer.loans.filter (fun loan => !covers ⟨0,total⟩ loan.ticket)}) =
      (clearLoans s).buffers := by
    apply List.ext_getElem?
    intro bid
    simp only [clearLoans,List.getElem?_map]
    cases hg : s.buffers[bid]? with
    | none => rfl
    | some buffer => simp only [Option.map_some,hfilter bid buffer hg]
  simp only [await,he,hc,Bool.not_true,bind,Except.bind,pure,Except.pure,hbuffers]
  rfl

theorem clear_returns (s : State) : Returned (clearLoans s) := by
  intro bid buffer hg
  simp only [clearLoans,List.getElem?_map] at hg
  cases hold : s.buffers[bid]? <;> simp only [hold,Option.map_none,Option.map_some] at hg
  · cases hg
  · cases hg; rfl

theorem clear_live {s} (hl : Preparation.Live s) : Preparation.Live (clearLoans s) := by
  intro bid buffer hg
  simp only [clearLoans,List.getElem?_map] at hg
  cases hold : s.buffers[bid]? with
  | none => simp [hold] at hg
  | some old =>
    simp only [hold,Option.map_some,Option.some.injEq] at hg
    subst buffer
    exact hl bid old hold

theorem drain_and_acquire {s commands event} (hr : Preparation.Ready s commands) (hi : Invariant s) (hp : Plain commands)
    (he : getEvent s event = .ok ⟨0,commands.length⟩) :
    ∃ final, run s (List.replicate commands.length (.device 0) ++ [.acquire event]) = .ok final ∧
      Returned final ∧ Preparation.Live final ∧ final.buffers.length = s.buffers.length ∧
      final.streams = [⟨commands.length,commands.length,[],[]⟩] := by
  obtain ⟨drained,hd,hs,hev,hm⟩ := drain_queue s commands.length 0 commands [] hr.1 hi hp
  have hcomplete : complete drained ⟨0,commands.length⟩ = true := by simp [complete,hs]
  have hevent : getEvent drained event = .ok ⟨0,commands.length⟩ := by simpa only [getEvent,hev] using he
  have ha := await_all_loans hevent hcomplete (metadata_bounded hm hr.2.2)
  refine ⟨clearLoans drained,?_,clear_returns _,clear_live (metadata_live hm hr.2.1),?_,?_⟩
  · simp only [Client.run_append,hd,Except.bind,run,step,ha]
  · simpa [clearLoans] using metadata_length hm
  · simpa only [clearLoans,Nat.zero_add] using hs

theorem returned_can_write {state : State} (hr : Returned state) (hl : Preparation.Live state)
    (bid value : Nat) (hb : bid < state.buffers.length) : ∃ next, hostWrite state bid value = .ok next := by
  have hg : state.buffers[bid]? = some state.buffers[bid] := List.getElem?_eq_getElem hb
  have hget := getBuffer_iff.mpr ⟨hg,hl bid _ hg⟩
  refine ⟨{state with buffers := state.buffers.set bid {state.buffers[bid] with value := value}},?_⟩
  simp [hostWrite,hget,hr bid _ hg,bind,Except.bind,pure,Except.pure]

theorem returned_can_reclaim {state : State} (hr : Returned state) (hl : Preparation.Live state)
    (bid : Nat) (hb : bid < state.buffers.length) : ∃ next, reclaim state bid = .ok next := by
  have hg : state.buffers[bid]? = some state.buffers[bid] := List.getElem?_eq_getElem hb
  have hget := getBuffer_iff.mpr ⟨hg,hl bid _ hg⟩
  refine ⟨{state with buffers := state.buffers.set bid {state.buffers[bid] with alive := false}},?_⟩
  simp [reclaim,hget,hr bid _ hg,bind,Except.bind,pure,Except.pure]

end Ptx.Async.Drain
