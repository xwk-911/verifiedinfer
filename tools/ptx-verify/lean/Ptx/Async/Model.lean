import Std

/-! Explicit host/device stream model. A record captures an issued frontier; only
FIFO device execution advances completion. Event IDs are single-use. Borrowed
resources return only after a successful host await. Cross-stream waits are queued,
so submitting a wait never fabricates completion. Values are abstract cells;
this module does not yet refine CUDA runtime or PTX machine execution.
-/
namespace Ptx.Async

structure Ticket where
  stream : Nat
  seq : Nat
  deriving Repr, DecidableEq, BEq
deriving instance ReflBEq, LawfulBEq for Ticket
inductive Mode | read | write deriving Repr, DecidableEq, BEq
deriving instance ReflBEq, LawfulBEq for Mode
structure Loan where
  ticket : Ticket
  mode : Mode
  deriving Repr, DecidableEq
structure Buffer where
  value : Nat := 0
  alive : Bool := true
  loans : List Loan := []
  deriving Repr, DecidableEq
inductive Command
  | copy (src dst : Nat)
  | use (buffer : Nat)
  | wait (ticket : Ticket)
  deriving Repr, DecidableEq
structure Stream where
  issued : Nat := 0
  completed : Nat := 0
  queue : List Command := []
  dependencies : List Ticket := []
  deriving Repr, DecidableEq
structure Event where
  id : Nat
  ticket : Ticket
  deriving Repr, DecidableEq
structure State where
  streams : List Stream
  buffers : List Buffer
  events : List Event := []
  deriving Repr, DecidableEq
inductive Error
  | invalidStream | invalidBuffer | invalidEvent | duplicateEvent
  | freed | outstandingLoan | notComplete | emptyQueue | alias
  deriving Repr, DecidableEq

private def require (o : Option α) (e : Error) : Except Error α :=
  match o with | some x => .ok x | none => .error e
@[simp] theorem require_some (x : α) (e : Error) : require (some x) e = .ok x := rfl
@[simp] theorem require_none (e : Error) : require (none : Option α) e = .error e := rfl
def getBuffer (s : State) (b : Nat) : Except Error Buffer := do
  let v ← require s.buffers[b]? .invalidBuffer
  if !v.alive then throw .freed
  return v
def getStream (s : State) (sid : Nat) : Except Error Stream :=
  require s.streams[sid]? .invalidStream
def getEvent (s : State) (id : Nat) : Except Error Ticket := do
  let e ← require (s.events.find? (fun e => e.id == id)) .invalidEvent
  return e.ticket
def complete (s : State) (t : Ticket) : Bool :=
  match s.streams[t.stream]? with
  | none => false
  | some stream => t.seq ≤ stream.completed
def covers (frontier old : Ticket) : Bool :=
  frontier.stream == old.stream && old.seq ≤ frontier.seq
def ordered (sid : Nat) (st : Stream) (old : Ticket) : Bool :=
  (old.stream == sid && old.seq ≤ st.issued) || st.dependencies.any (fun t => covers t old)
def mayBorrow (sid : Nat) (st : Stream) (mode : Mode) (b : Buffer) : Bool :=
  b.loans.all (fun old => (mode == .read && old.mode == .read) || ordered sid st old.ticket)

/-- The common permission protocol for copy, compute use and deferred reclamation. -/
def borrow (s : State) (sid bid : Nat) (mode : Mode) : Except Error State := do
  let st ← getStream s sid
  let b ← getBuffer s bid
  if !mayBorrow sid st mode b then throw .outstandingLoan
  let loan : Loan := ⟨⟨sid,st.issued+1⟩,mode⟩
  return { s with buffers := s.buffers.set bid { b with loans := loan::b.loans } }
def enqueue (s : State) (sid : Nat) (c : Command) : Except Error State := do
  let st ← getStream s sid
  return { s with streams := s.streams.set sid { st with issued := st.issued+1, queue := st.queue ++ [c] } }
def submitCopy (s : State) (sid src dst : Nat) : Except Error State := do
  if src == dst then throw .alias
  let s ← borrow s sid src .read
  let s ← borrow s sid dst .write
  enqueue s sid (.copy src dst)
def submitUse (s : State) (sid bid : Nat) : Except Error State := do
  let s ← borrow s sid bid .read
  enqueue s sid (.use bid)
def record (s : State) (sid id : Nat) : Except Error State := do
  let st ← getStream s sid
  if s.events.any (fun e => e.id == id) then throw .duplicateEvent
  return { s with events := ⟨id,⟨sid,st.issued⟩⟩ :: s.events }
def waitStream (s : State) (sid id : Nat) : Except Error State := do
  let t ← getEvent s id
  let s ← enqueue s sid (.wait t)
  let st ← getStream s sid
  return { s with streams := s.streams.set sid { st with dependencies := t::st.dependencies } }

/-- Command execution changes data, while queue progress belongs to deviceStep. -/
def execute (s : State) (c : Command) : Except Error State := do
  match c with
    | .wait t => if complete s t then pure s else throw .notComplete
    | .use bid => do
      let _ ← getBuffer s bid
      pure s
    | .copy src dst => do
      let a ← getBuffer s src
      let b ← getBuffer s dst
      pure { s with buffers := s.buffers.set dst { b with value := a.value } }

/-- Device execution performs actual FIFO work; a wait is blocked until its event completes. -/
def deviceStep (s : State) (sid : Nat) : Except Error State := do
  let st ← getStream s sid
  let c ← require st.queue.head? .emptyQueue
  let s ← execute s c
  return { s with streams := s.streams.set sid { st with completed := st.completed+1, queue := st.queue.drop 1 } }

/-- Acquiring an event returns only loans whose commands precede its recorded frontier. -/
def await (s : State) (id : Nat) : Except Error State := do
  let t ← getEvent s id
  if !complete s t then throw .notComplete
  return { s with buffers := s.buffers.map (fun b => { b with loans := b.loans.filter (fun l => !covers t l.ticket) }) }
def reclaim (s : State) (bid : Nat) : Except Error State := do
  let b ← getBuffer s bid
  if !b.loans.isEmpty then throw .outstandingLoan
  return { s with buffers := s.buffers.set bid { b with alive := false } }
def hostWrite (s : State) (bid value : Nat) : Except Error State := do
  let b ← getBuffer s bid
  if !b.loans.isEmpty then throw .outstandingLoan
  return { s with buffers := s.buffers.set bid { b with value := value } }

theorem reclaim_rejects_loan {s bid b} (hb : getBuffer s bid = .ok b)
    (hloan : b.loans.isEmpty = false) : reclaim s bid = .error .outstandingLoan := by
  simp [reclaim, hb, hloan, bind, Except.bind, pure, Except.pure, throw, throwThe]
  rfl

theorem await_requires_completion {s id s'} (h : await s id = .ok s') :
    ∃ t, getEvent s id = .ok t ∧ complete s t = true := by
  unfold await at h
  cases he : getEvent s id with
  | error e => simp [he, bind, Except.bind] at h
  | ok t =>
    refine ⟨t, rfl, ?_⟩
    cases hc : complete s t <;> simp [he, hc, bind, Except.bind, pure, Except.pure, throw, throwThe] at h ⊢

theorem record_preserves_completion {s sid id s'} (h : record s sid id = .ok s') :
    s'.streams = s.streams := by
  unfold record at h
  cases hs : getStream s sid with
  | error e => simp [hs, bind, Except.bind] at h
  | ok st =>
    by_cases hd : s.events.any (fun e => e.id == id)
    · simp [hs, hd, bind, Except.bind, pure, Except.pure, throw, throwThe] at h
    · simp [hs, hd, bind, Except.bind, pure, Except.pure] at h
      subst s'; rfl

/-- Public protocol actions. borrow/enqueue/execute are internal construction
steps, not independent host actions that may bypass resource acquisition. -/
inductive Action where
  | copy (sid src dst : Nat)
  | use (sid buffer : Nat)
  | record (sid event : Nat)
  | wait (sid event : Nat)
  | device (sid : Nat)
  | acquire (event : Nat)
  | reclaim (buffer : Nat)
  | write (buffer value : Nat)
  deriving Repr, DecidableEq

def step (s : State) : Action → Except Error State
  | .copy sid src dst => submitCopy s sid src dst
  | .use sid bid => submitUse s sid bid
  | .record sid event => record s sid event
  | .wait sid event => waitStream s sid event
  | .device sid => deviceStep s sid
  | .acquire event => await s event
  | .reclaim bid => reclaim s bid
  | .write bid value => hostWrite s bid value

inductive Steps : State → State → Prop
  | refl (s) : Steps s s
  | next {s s' s''} (a) : step s a = .ok s' → Steps s' s'' → Steps s s''

def run : State → List Action → Except Error State
  | s, [] => .ok s
  | s, a::as => (step s a).bind (fun s' => run s' as)

def initial (streamCount : Nat) (values : List Nat) : State := {
  streams := List.replicate streamCount {}
  buffers := values.map (fun v => {value := v})
}

theorem run_sound {s actions s'} (h : run s actions = .ok s') : Steps s s' := by
  induction actions generalizing s with
  | nil => simp [run] at h; subst s'; exact .refl s
  | cons a as ih =>
    simp only [run] at h
    cases hs : step s a with
    | error e => simp [hs,Except.bind] at h
    | ok mid => exact .next a hs (ih (by simpa [hs,Except.bind] using h))

end Ptx.Async
