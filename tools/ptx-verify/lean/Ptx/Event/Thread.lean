import Ptx.Semantics
import Ptx.ISA.Launch
import Ptx.ISA.Bytes
import Ptx.ISA.Scope

/-! Deterministic oracle-driven traces for the SAME generated integer programs.
This is candidate generation, not memory consistency or a correctness verdict.
Loads do not consult a global mutable heap. Barriers emit arrival/return pairs;
their global matching must be checked separately before a candidate is admitted.
Only tid.x is available in the original AST; geometry does not add instructions.
-/
namespace Ptx.Event
open Ptx.ISA

/-- One RMW reads and writes the same bytes. Equal size is carried by the data,
not assumed later by a kernel's correctness proof. -/
structure RmwBytes (ByteValue : Type) where
  before : List ByteValue
  after : List ByteValue
  sameSize : before.length = after.length
  deriving Repr, DecidableEq

inductive Kind (ByteValue : Type := Byte)
  | read (location : Location) (bytes : List ByteValue)
  | write (location : Location) (bytes : List ByteValue)
  | rmw (scope : Scope) (location : Location) (bytes : RmwBytes ByteValue)
  | barrierArrival (id generation : Nat)
  | barrierReturn (id generation : Nat)
  deriving Repr, DecidableEq

structure Context where
  id : ThreadId
  params : Bindings := []
  deriving Repr, DecidableEq

structure State where
  thread : Ptx.Thread := {}
  queries : Nat := 0
  generations : List (Nat × Nat) := []
  deriving Repr, DecidableEq

abbrev Oracle := Nat → Nat

def generation (s : State) (id : Nat) : Nat :=
  ((s.generations.find? (fun p => p.1 == id)).map Prod.snd).getD 0

def step (ctx : Context) (oracle : Oracle) (code : List Instr) (s : State) :
    Except Fault (State × List Kind) := do
  let t := s.thread
  if t.status != .running then throw .blocked
  let i ← match code[t.pc]? with
    | some i => .ok i
    | none => .error (.invalidPC t.pc)
  match i with
  | .load space dst address =>
    let addr ← evalAddr ctx.id.tid.x t address
    let value := wrap 32 (oracle s.queries)
    return ({ s with thread := assign t dst value, queries := s.queries + 1 },
      [.read (Location.resolve space ctx.id addr) (encodeU32 value)])
  | .store space address operand =>
    let addr ← evalAddr ctx.id.tid.x t address
    let value ← eval ctx.id.tid.x t operand
    return ({ s with thread := advance t },
      [.write (Location.resolve space ctx.id addr) (encodeU32 value)])
  | .barrier id =>
    let g := generation s id
    let visits := (id, g+1) :: s.generations.filter (fun p => p.1 != id)
    let next := { s with thread := advance t, generations := visits }
    return (next,
      [.barrierArrival id g, .barrierReturn id g])
  | i =>
    let next ← localStep ctx.params ctx.id.tid.x t i
    return ({ s with thread := next }, [])

/-- Exactly n steps: successful prefixes may be incomplete. Exiting is explicit. -/
def run (ctx : Context) (oracle : Oracle) (code : List Instr) :
    Nat → State → Except Fault (State × List Kind)
  | 0, s => .ok (s, [])
  | n+1, s =>
    (step ctx oracle code s).bind fun result =>
      (run ctx oracle code n result.1).bind fun tail =>
        .ok (tail.1, result.2 ++ tail.2)

inductive Runs (ctx : Context) (oracle : Oracle) (code : List Instr) :
    State → List Kind → State → Prop
  | nil (s) : Runs ctx oracle code s [] s
  | cons {s mid last first rest} : step ctx oracle code s = .ok (mid, first) →
      Runs ctx oracle code mid rest last → Runs ctx oracle code s (first ++ rest) last

theorem run_sound {ctx oracle code n s last events}
    (h : run ctx oracle code n s = .ok (last, events)) :
    Runs ctx oracle code s events last := by
  induction n generalizing s last events with
  | zero =>
    simp only [run, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact .nil _
  | succ n ih =>
    cases hs : step ctx oracle code s with
    | error e => simp [run, hs, Except.bind] at h
    | ok result =>
      rcases result with ⟨mid, first⟩
      cases hr : run ctx oracle code n mid with
      | error e => simp [run, hs, hr, Except.bind] at h
      | ok result =>
        rcases result with ⟨last', rest⟩
        simp only [run, hs, hr, Except.bind,
          Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact .cons hs (ih hr)

theorem runs_append {ctx oracle code s mid last first rest}
    (ha : Runs ctx oracle code s first mid) (hb : Runs ctx oracle code mid rest last) :
    Runs ctx oracle code s (first ++ rest) last := by
  induction ha with
  | nil => exact hb
  | cons hs _ ih => simpa only [List.append_assoc] using Runs.cons hs (ih hb)

/-- Register-only instructions retain their existing meaning, independent of the
oracle. This deliberately excludes memory and barrier instructions. -/
theorem local_step {ctx oracle code s i next}
    (hr : s.thread.status = .running) (hp : code[s.thread.pc]? = some i)
    (hm : isLocal i = true) (hb : ∀ id, i ≠ .barrier id)
    (hs : localStep ctx.params ctx.id.tid.x s.thread i = .ok next) :
    step ctx oracle code s = .ok ({ s with thread := next }, []) := by
  cases i <;> simp_all [isLocal, step, bind, Except.bind, pure, Except.pure]

end Ptx.Event
