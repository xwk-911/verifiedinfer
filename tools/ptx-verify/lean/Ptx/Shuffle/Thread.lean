import Ptx.Shuffle.Syntax
import Ptx.Scalar.Thread

/-! Actual shuffle source traces. Each operation records its input, mode,
member mask and a per-(mode,mask) generation. Both result value and optional
predicate come from an oracle; global agreement constrains them only for a
defined matched group. Undefined/inactive sources are not silently zeroed.
-/
namespace Ptx.Shuffle
open Ptx.ISA
noncomputable section

structure Key where
  mode : Mode
  mask : Nat
  deriving Repr, DecidableEq, BEq
deriving instance ReflBEq, LawfulBEq for Key
structure Record where
  key : Key
  generation : Nat
  pc : Nat
  input : Nat
  b : Nat
  c : Nat
  reply : Nat
  replyPredicate : Bool
  deriving Repr, DecidableEq
inductive Kind
  | ordinary (event : Scalar.Kind)
  | shuffle (record : Record)

structure Oracle where
  memory : Scalar.Oracle
  shuffle : Nat → Nat × Bool
structure State where
  base : Scalar.State := {}
  queries : Nat := 0
  visits : List (Key × Nat) := []

def generation (state : State) (key : Key) := ((state.visits.find? (fun item => item.1 == key)).map Prod.snd).getD 0
def advanceVisits (state : State) (key : Key) := (key,generation state key+1)::state.visits.filter (fun item => item.1 != key)
def writeResult (state : Scalar.State) (dst : String) (predicate : Option String) (value : Nat) (valid : Bool) : Scalar.State :=
  let next := {state.core with thread := assign state.core.thread dst (wrap 32 value)}
  let next := match predicate with
    | none => next
    | some name => {next with thread := {next.thread with regs := put name (if valid then 1 else 0) next.thread.regs}}
  Scalar.finishInteger state next

def step (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) (state : State) : Except Scalar.Fault (State × List Kind) := do
  if state.base.core.thread.status != .running then throw (.integer .blocked)
  let instruction ← Scalar.require (code[state.base.core.thread.pc]?) (.integer (.invalidPC state.base.core.thread.pc))
  match instruction with
  | .scalar _ =>
      let result ← Scalar.step ctx oracle.memory (scalarSkeleton code) state.base
      return ({state with base := result.1},result.2.map Kind.ordinary)
  | .shfl mode dst predicate a b c mask =>
      let input ← Scalar.liftInteger (Ptx.eval ctx.id.tid.x state.base.core.thread a)
      let offset ← Scalar.liftInteger (Ptx.eval ctx.id.tid.x state.base.core.thread b)
      let clamp ← Scalar.liftInteger (Ptx.eval ctx.id.tid.x state.base.core.thread c)
      let participants ← Scalar.liftInteger (Ptx.eval ctx.id.tid.x state.base.core.thread mask)
      let key : Key := ⟨mode,wrap 32 participants⟩
      let answer := oracle.shuffle state.queries
      let event : Record := ⟨key,generation state key,state.base.core.thread.pc,wrap 32 input,wrap 32 offset,wrap 32 clamp,wrap 32 answer.1,answer.2⟩
      return (⟨writeResult state.base dst predicate answer.1 answer.2,state.queries+1,advanceVisits state key⟩,[.shuffle event])

def run (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) : Nat → State → Except Scalar.Fault (State × List Kind)
  | 0,state => .ok (state,[])
  | n+1,state => (step ctx oracle code state).bind fun first => (run ctx oracle code n first.1).bind fun rest => .ok (rest.1,first.2++rest.2)

inductive Runs (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) : State → List Kind → State → Prop
  | nil state : Runs ctx oracle code state [] state
  | cons {state mid final first rest} : step ctx oracle code state = .ok (mid,first) → Runs ctx oracle code mid rest final →
      Runs ctx oracle code state (first++rest) final

theorem run_sound {ctx oracle code n state final events} (hr : run ctx oracle code n state = .ok (final,events)) : Runs ctx oracle code state events final := by
  induction n generalizing state events with
  | zero => cases hr; exact .nil _
  | succ n ih =>
    change (step ctx oracle code state).bind _ = .ok (final,events) at hr
    cases hs : step ctx oracle code state with
    | error error => simp [hs,Except.bind] at hr
    | ok first =>
      cases ht : run ctx oracle code n first.1 with
      | error error => simp [hs,ht,Except.bind] at hr
      | ok rest =>
        have he : (rest.1,first.2++rest.2) = (final,events) := Except.ok.inj (by simpa only [hs,ht,Except.bind] using hr)
        cases he
        exact .cons hs (ih ht)

theorem run_add (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) (n m : Nat) (state : State) :
    run ctx oracle code (n+m) state = (run ctx oracle code n state).bind (fun first =>
      (run ctx oracle code m first.1).map (fun rest => (rest.1,first.2++rest.2))) := by
  induction n generalizing state with
  | zero =>
      simp only [Nat.zero_add,run,Except.bind,List.nil_append]
      cases run ctx oracle code m state <;> rfl
  | succ n ih =>
    simp only [Nat.succ_add,run]
    cases hs : step ctx oracle code state with
    | error error => rfl
    | ok first =>
      simp only [Except.bind]
      rw [ih]
      cases hn : run ctx oracle code n first.1 with
      | error error => rfl
      | ok mid =>
        cases hm : run ctx oracle code m mid.1 with
        | error error => simp only [Except.bind,Except.map,hm]
        | ok last => simp only [Except.bind,Except.map,hm,List.append_assoc]

end
end Ptx.Shuffle
