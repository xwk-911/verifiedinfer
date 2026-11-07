import Ptx.Async.Shape

/-! Readiness of public single-stream preparation, before device execution.
All old loans belong to this stream and an already issued ticket. Readiness
is derived from the real borrow/enqueue interpreter, not an assumed success.
-/
namespace Ptx.Async.Preparation

def Live (s : State) : Prop := ∀ (bid : Nat) (buffer : Buffer), s.buffers[bid]? = some buffer → buffer.alive = true
def Bounded (s : State) (limit : Nat) : Prop := ∀ (bid : Nat) (buffer : Buffer), s.buffers[bid]? = some buffer →
  ∀ (loan : Loan), loan ∈ buffer.loans → loan.ticket.stream = 0 ∧ loan.ticket.seq ≤ limit
def Ready (s : State) (commands : List Command) : Prop :=
  s.streams = [⟨commands.length,0,commands,[]⟩] ∧ Live s ∧ Bounded s commands.length

def withLoan (s : State) (bid : Nat) (buffer : Buffer) (loan : Loan) : State :=
  {s with buffers := s.buffers.set bid {buffer with loans := loan::buffer.loans}}

theorem bounded_mono {s before after} (hb : Bounded s before) (hle : before ≤ after) : Bounded s after := by
  intro bid buffer hg loan hl
  have h := hb bid buffer hg loan hl
  exact ⟨h.1,Nat.le_trans h.2 hle⟩

theorem withLoan_live {s bid buffer loan} (hl : Live s) (hg : s.buffers[bid]? = some buffer) : Live (withLoan s bid buffer loan) := by
  intro other actual ha
  by_cases he : other = bid
  · subst other
    have hlt := (List.getElem?_eq_some_iff.mp hg).1
    have hx : actual = {buffer with loans := loan::buffer.loans} := by simpa [withLoan,List.getElem?_set_self hlt] using ha.symm
    subst actual
    exact hl bid buffer hg
  · exact hl other actual (by simpa [withLoan,List.getElem?_set_ne (Ne.symm he)] using ha)

theorem withLoan_bounded {s bid buffer loan limit} (hb : Bounded s limit) (hg : s.buffers[bid]? = some buffer)
    (hn : loan.ticket.stream = 0 ∧ loan.ticket.seq ≤ limit) : Bounded (withLoan s bid buffer loan) limit := by
  intro other actual ha old ho
  by_cases he : other = bid
  · subst other
    have hlt := (List.getElem?_eq_some_iff.mp hg).1
    have hx : actual = {buffer with loans := loan::buffer.loans} := by simpa [withLoan,List.getElem?_set_self hlt] using ha.symm
    subst actual
    rcases List.mem_cons.mp ho with rfl | ho
    · exact hn
    · exact hb bid buffer hg old ho
  · exact hb other actual (by simpa [withLoan,List.getElem?_set_ne (Ne.symm he)] using ha) old ho

theorem ready_initial (values : List Nat) : Ready (initial 1 values) [] := by
  refine ⟨rfl,?_,?_⟩
  · intro bid buffer hg
    rw [initial,List.getElem?_map] at hg
    cases hv : values[bid]? <;> simp only [hv,Option.map_none,Option.map_some] at hg
    · cases hg
    · cases hg; rfl
  · intro bid buffer hg loan hl
    rw [initial,List.getElem?_map] at hg
    cases hv : values[bid]? <;> simp only [hv,Option.map_none,Option.map_some] at hg
    · cases hg
    · cases hg; cases hl

theorem ready_buffer {s commands} (hr : Ready s commands) (bid : Nat) (hb : bid < s.buffers.length) :
    ∃ buffer, getBuffer s bid = .ok buffer := by
  have hg : s.buffers[bid]? = some s.buffers[bid] := List.getElem?_eq_getElem hb
  exact ⟨_,getBuffer_iff.mpr ⟨hg,hr.2.1 bid _ hg⟩⟩

theorem ready_mayBorrow {s commands bid buffer mode} (hr : Ready s commands) (hg : getBuffer s bid = .ok buffer) :
    mayBorrow 0 ⟨commands.length,0,commands,[]⟩ mode buffer = true := by
  apply List.all_eq_true.mpr
  intro loan hl
  have h := hr.2.2 bid buffer (getBuffer_iff.mp hg).1 loan hl
  simp [ordered,h.1,h.2]

theorem ready_use {s commands bid} (hr : Ready s commands) (hb : bid < s.buffers.length) :
    ∃ next, step s (.use 0 bid) = .ok next ∧ Ready next (commands++[.use bid]) ∧ next.events = s.events := by
  obtain ⟨buffer,hget⟩ := ready_buffer hr bid hb
  have hlookup := (getBuffer_iff.mp hget).1
  have hstream : getStream s 0 = .ok ⟨commands.length,0,commands,[]⟩ := by simp [getStream_iff,hr.1]
  let mid := withLoan s bid buffer ⟨⟨0,commands.length+1⟩,.read⟩
  let next : State := {mid with streams := [⟨commands.length+1,0,commands++[.use bid],[]⟩]}
  have hborrow : borrow s 0 bid .read = .ok mid := by
    simp [borrow,hstream,hget,ready_mayBorrow (mode := .read) hr hget,mid,withLoan,bind,Except.bind,pure,Except.pure]
  have hmidstream : getStream mid 0 = .ok ⟨commands.length,0,commands,[]⟩ := hstream
  have he : enqueue mid 0 (.use bid) = .ok next := by
    simp only [enqueue,hmidstream,bind,Except.bind,pure,Except.pure]
    simp [hr.1,mid,withLoan,next]
  refine ⟨next,by simpa [step,submitUse,hborrow,bind,Except.bind] using he,?_,rfl⟩
  refine ⟨by simp [next],withLoan_live hr.2.1 hlookup,?_⟩
  simpa only [Bounded,next,mid,withLoan,List.length_append,List.length_singleton] using
    (withLoan_bounded (bounded_mono hr.2.2 (Nat.le_add_right _ 1)) hlookup ⟨rfl,Nat.le_refl _⟩)

theorem ready_access {s commands bid} (mode : Mode) (hr : Ready s commands) (hb : bid < s.buffers.length) :
    ∃ next, step s (.access 0 bid mode) = .ok next ∧ Ready next (commands++[.access bid mode]) ∧ next.events = s.events := by
  obtain ⟨buffer,hget⟩ := ready_buffer hr bid hb
  have hlookup := (getBuffer_iff.mp hget).1
  have hstream : getStream s 0 = .ok ⟨commands.length,0,commands,[]⟩ := by simp [getStream_iff,hr.1]
  let mid := withLoan s bid buffer ⟨⟨0,commands.length+1⟩,mode⟩
  let next : State := {mid with streams := [⟨commands.length+1,0,commands++[.access bid mode],[]⟩]}
  have hborrow : borrow s 0 bid mode = .ok mid := by
    simp [borrow,hstream,hget,ready_mayBorrow (mode := mode) hr hget,mid,withLoan,bind,Except.bind,pure,Except.pure]
  have hmidstream : getStream mid 0 = .ok ⟨commands.length,0,commands,[]⟩ := hstream
  have he : enqueue mid 0 (.access bid mode) = .ok next := by
    simp only [enqueue,hmidstream,bind,Except.bind,pure,Except.pure]
    simp [hr.1,mid,withLoan,next]
  refine ⟨next,by simpa [step,submitAccess,hborrow,bind,Except.bind] using he,?_,rfl⟩
  refine ⟨by simp [next],withLoan_live hr.2.1 hlookup,?_⟩
  simpa only [Bounded,next,mid,withLoan,List.length_append,List.length_singleton] using
    (withLoan_bounded (bounded_mono hr.2.2 (Nat.le_add_right _ 1)) hlookup ⟨rfl,Nat.le_refl _⟩)

theorem ready_copy {s commands src dst} (hr : Ready s commands) (ha : src < s.buffers.length) (hb : dst < s.buffers.length)
    (hne : src ≠ dst) :
    ∃ next, step s (.copy 0 src dst) = .ok next ∧ Ready next (commands++[.copy src dst]) ∧ next.events = s.events := by
  obtain ⟨a,hga⟩ := ready_buffer hr src ha
  obtain ⟨b,hgb⟩ := ready_buffer hr dst hb
  have hla := (getBuffer_iff.mp hga).1
  have hlb := (getBuffer_iff.mp hgb).1
  have hstream : getStream s 0 = .ok ⟨commands.length,0,commands,[]⟩ := by simp [getStream_iff,hr.1]
  let first := withLoan s src a ⟨⟨0,commands.length+1⟩,.read⟩
  let second := withLoan first dst b ⟨⟨0,commands.length+1⟩,.write⟩
  let next : State := {second with streams := [⟨commands.length+1,0,commands++[.copy src dst],[]⟩]}
  have hfirst : borrow s 0 src .read = .ok first := by
    simp [borrow,hstream,hga,ready_mayBorrow (mode := .read) hr hga,first,withLoan,bind,Except.bind,pure,Except.pure]
  have hfirststream : getStream first 0 = .ok ⟨commands.length,0,commands,[]⟩ := hstream
  have hother : getBuffer first dst = .ok b := getBuffer_iff.mpr
    ⟨by simpa [first,withLoan,List.getElem?_set_ne hne] using hlb,(getBuffer_iff.mp hgb).2⟩
  have hsecond : borrow first 0 dst .write = .ok second := by
    simp [borrow,hfirststream,hother,ready_mayBorrow (mode := .write) hr hgb,second,withLoan,bind,Except.bind,pure,Except.pure]
  have hsecondstream : getStream second 0 = .ok ⟨commands.length,0,commands,[]⟩ := hstream
  have he : enqueue second 0 (.copy src dst) = .ok next := by
    simp only [enqueue,hsecondstream,bind,Except.bind,pure,Except.pure]
    simp [hr.1,first,second,withLoan,next]
  refine ⟨next,by simpa [step,submitCopy,hne,hfirst,hsecond,bind,Except.bind] using he,?_,rfl⟩
  have hfirstlive := withLoan_live hr.2.1 hla (loan := ⟨⟨0,commands.length+1⟩,.read⟩)
  have hfirstbound := withLoan_bounded (bounded_mono hr.2.2 (Nat.le_add_right _ 1)) hla
    (loan := ⟨⟨0,commands.length+1⟩,.read⟩) ⟨rfl,Nat.le_refl _⟩
  have hlookup : first.buffers[dst]? = some b := (getBuffer_iff.mp hother).1
  refine ⟨by simp [next],withLoan_live hfirstlive hlookup,?_⟩
  simpa only [Bounded,next,second,first,withLoan,List.length_append,List.length_singleton] using
    (withLoan_bounded hfirstbound hlookup (loan := ⟨⟨0,commands.length+1⟩,.write⟩) ⟨rfl,Nat.le_refl _⟩)

theorem ready_record {s commands event} (hr : Ready s commands)
    (hf : s.events.any (fun entry => entry.id == event) = false) :
    step s (.record 0 event) = .ok {s with events := ⟨event,⟨0,commands.length⟩⟩::s.events} := by
  have hstream : getStream s 0 = .ok ⟨commands.length,0,commands,[]⟩ := by simp [getStream_iff,hr.1]
  simp [step,record,hstream,hf,bind,Except.bind,pure,Except.pure]

inductive Request
  | use (buffer : Nat)
  | access (buffer : Nat) (mode : Mode)
  | copy (src dst : Nat)

def Request.command : Request → Command
  | .use bid => .use bid
  | .access bid mode => .access bid mode
  | .copy src dst => .copy src dst
def Request.action : Request → Action
  | .use bid => .use 0 bid
  | .access bid mode => .access 0 bid mode
  | .copy src dst => .copy 0 src dst
def Request.Valid (buffers : Nat) : Request → Prop
  | .use bid => bid < buffers
  | .access bid _ => bid < buffers
  | .copy src dst => src < buffers ∧ dst < buffers ∧ src ≠ dst

theorem ready_requests {s commands} (hr : Ready s commands) (requests : List Request)
    (hv : ∀ request ∈ requests, request.Valid s.buffers.length) :
    ∃ next, run s (requests.map Request.action) = .ok next ∧ Ready next (commands++requests.map Request.command) ∧
      next.buffers.length = s.buffers.length ∧ next.events = s.events := by
  induction requests generalizing s commands with
  | nil => exact ⟨s,rfl,by simpa using hr,rfl,rfl⟩
  | cons request rest ih =>
    have hvalid := hv request (by simp)
    have hstep : ∃ mid, step s request.action = .ok mid ∧ Ready mid (commands++[request.command]) ∧ mid.events = s.events := by
      cases request with
      | use bid => exact ready_use hr hvalid
      | access bid mode => exact ready_access mode hr hvalid
      | copy src dst => exact ready_copy hr hvalid.1 hvalid.2.1 hvalid.2.2
    obtain ⟨mid,hs,hm,he⟩ := hstep
    have hlen := step_buffers_length hs
    obtain ⟨next,hn,hr',hlen',he'⟩ := ih hm (by intro actual ha; simpa only [hlen] using hv actual (by simp [ha]))
    refine ⟨next,by simpa [List.map_cons,run,hs,Except.bind] using hn,?_,hlen'.trans hlen,he'.trans he⟩
    simpa only [List.map_cons,List.append_assoc,List.singleton_append] using hr'

end Ptx.Async.Preparation
