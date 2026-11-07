import Ptx.Hopper.Thread
import Ptx.Hopper.WgmmaAccess

/-! Source-local WGMMA execution on the same Hopper AST, delegating every
ordinary step at its actual PC to Hopper.step. Register writes become visible
only at an acknowledged committed-group wait; issue consumes an unconstrained
arithmetic reply. Warpgroup participation, shared operand byte reads, descriptor
layout, exact-real collective arithmetic and memory admission are separate. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section

structure Mark where
  pc : Nat
  sequence : Nat
  warpgroup : Nat
  deriving Repr, DecidableEq
structure Call where
  ordinal : Nat
  group : Nat
  lane : Fin 128
  d : Ampere.Registers4
  a : Nat
  b : Nat
  scaleD : Bool
  input : Fin 4 → ℝ
  output : Fin 4 → ℝ
  query : Nat
  /-- Logical A bytes 0..2047 then B bytes 2048..2303; locations derive from
  this call's descriptors. These replies still require byte-level admission. -/
  operandBytes : Nat → Symbolic.Byte := fun _ => .bits (byte 0)
structure Ledger where
  fenced : Bool := false
  dirty : List String := []
  groups : Nat := 0
  completed : Nat := 0
  calls : List Call := []
  syncs : Nat := 0
structure State where
  base : Hopper.State := {}
  ledger : Ledger := {}
structure Oracle where
  base : Hopper.Oracle
  matrix : Nat → Fin 4 → ℝ := fun _ _ => 0
  completed : Nat → Nat := fun _ => 0
  operands : Nat → Nat → Symbolic.Byte := fun _ _ => .bits (byte 0)
inductive Event
  | base (event : Hopper.Event)
  | fence (mark : Mark)
  | mma (mark : Mark) (call : Call)
  | commit (mark : Mark) (group : Nat)
  | wait (mark : Mark) (groups keep before after query : Nat)
inductive Fault
  | base (fault : Hopper.Fault)
  | integer (fault : Ptx.Fault)
  | scalar (fault : Scalar.Fault)
  | blocked
  | invalidPC (pc : Nat)
  | pendingRegister (name : String)
  | needsFence
  | dirtyRegister (name : String)
  | duplicateAccumulator
  | waitCount (keep : Nat)
  deriving Repr, DecidableEq

def liftBase : Except Hopper.Fault α → Except Fault α
  | .ok v => .ok v | .error e => .error (.base e)
def liftInteger : Except Ptx.Fault α → Except Fault α
  | .ok v => .ok v | .error e => .error (.integer e)
def liftScalar : Except Scalar.Fault α → Except Fault α
  | .ok v => .ok v | .error e => .error (.scalar e)

def mark (ctx : Scalar.Context) (s : State) : Mark :=
  ⟨s.base.scalar.core.thread.pc,s.ledger.syncs,Ampere.linearThread ctx / 128⟩
def pending (ledger : Ledger) : List Call := ledger.calls.filter (fun call => ledger.completed ≤ call.group)
def pendingNames (ledger : Ledger) : List String := (pending ledger).flatMap (fun call => call.d.names)
def pendingValue (ledger : Ledger) (name : String) : Option ℝ :=
  (pending ledger).foldl (fun old call =>
    if name = call.d.r0 then some (call.output 0) else if name = call.d.r1 then some (call.output 1)
    else if name = call.d.r2 then some (call.output 2) else if name = call.d.r3 then some (call.output 3) else old) none

def evalAccumulator (s : State) (name : String) : Except Fault ℝ :=
  match pendingValue s.ledger name with
  | some value => .ok value
  | none => liftScalar (Scalar.eval .f32 s.base.scalar (.reg name))
def readAccumulator (s : State) (d : Ampere.Registers4) : Except Fault (Fin 4 → ℝ) := do
  let a ← evalAccumulator s d.r0
  let b ← evalAccumulator s d.r1
  let c ← evalAccumulator s d.r2
  let e ← evalAccumulator s d.r3
  pure (fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else e)

def readScaledAccumulator (s : State) (d : Ampere.Registers4) (scale : Nat) : Except Fault (Fin 4 → ℝ) :=
  if scale != 0 then readAccumulator s d else pure (fun _ => 0)

/-- No PC/query/MMA counter is advanced by asynchronous writeback. -/
def writeResult (s : Hopper.State) (call : Call) : Hopper.State := {
  s with
  scalar := {
    s.scalar with
    core := {s.scalar.core with thread := {s.scalar.core.thread with regs := s.scalar.core.thread.regs.filter (fun kv => !call.d.names.contains kv.1)}}
    floats := [(call.d.r0,(.f32,call.output 0)),(call.d.r1,(.f32,call.output 1)),(call.d.r2,(.f32,call.output 2)),(call.d.r3,(.f32,call.output 3))] ++
      s.scalar.floats.filter (fun kv => !call.d.names.contains kv.1)
  }
  packed := s.packed.filter (fun kv => !call.d.names.contains kv.1)
}

def completionCut (ledger : Ledger) (keep reply : Nat) : Nat :=
  max ledger.completed (max (ledger.groups-keep) (min ledger.groups reply))
def waitState (s : State) (keep reply : Nat) : State :=
  let cut := completionCut s.ledger keep reply
  let finishing := s.ledger.calls.filter (fun call => s.ledger.completed ≤ call.group ∧ call.group < cut)
  let written := finishing.foldl writeResult s.base
  let next := Ampere.advance written
  {base := {next with scalar := {next.scalar with core := {next.scalar.core with queries := s.base.scalar.core.queries+1}}},
   ledger := {s.ledger with completed := cut,syncs := s.ledger.syncs+1}}

def makeCall (ctx : Scalar.Context) (s : State) (oracle : Oracle) (d : Ampere.Registers4)
    (pa pb : Nat) (useD : Bool) (input : Fin 4 → ℝ) : Call := {
  ordinal := s.ledger.calls.length
  group := s.ledger.groups
  lane := ⟨Ampere.linearThread ctx % 128,Nat.mod_lt _ (by decide)⟩
  d := d
  a := wrap 64 pa
  b := wrap 64 pb
  scaleD := useD
  input := input
  output := oracle.matrix s.base.scalar.core.queries
  query := s.base.scalar.core.queries
  operandBytes := oracle.operands s.base.scalar.core.queries
}
def issueState (s : State) (call : Call) : State :=
  let advanced := Ampere.advance s.base
  let next := {advanced with scalar := {advanced.scalar with core := {advanced.scalar.core with queries := s.base.scalar.core.queries+1}}}
  {base := next,ledger := {s.ledger with calls := s.ledger.calls++[call],syncs := s.ledger.syncs+1}}

def step (ctx : Scalar.Context) (oracle : Oracle) (code : List Hopper.Instr) (s : State) : Except Fault (State × List Event) := do
  if s.base.scalar.core.thread.status != .running then throw .blocked
  let instruction ← match code[s.base.scalar.core.thread.pc]? with
    | none => .error (.invalidPC s.base.scalar.core.thread.pc) | some i => .ok i
  match instruction with
  | .wgmma .fence =>
    pure ({base := Ampere.advance s.base,ledger := {s.ledger with fenced := true,dirty := [],syncs := s.ledger.syncs+1}},[.fence (mark ctx s)])
  | .wgmma .commit =>
    pure ({base := Ampere.advance s.base,ledger := {s.ledger with groups := s.ledger.groups+1,syncs := s.ledger.syncs+1}},[.commit (mark ctx s) s.ledger.groups])
  | .wgmma (.wait keep) =>
    if 8 ≤ keep then throw (.waitCount keep)
    let q := s.base.scalar.core.queries
    let next := waitState s keep (oracle.completed q)
    pure (next,[.wait (mark ctx s) s.ledger.groups keep s.ledger.completed next.ledger.completed q])
  | .wgmma (.mma d a b scaleD) =>
    if !s.ledger.fenced then throw .needsFence
    if !d.names.Nodup then throw .duplicateAccumulator
    match d.names.find? (fun name => s.ledger.dirty.contains name) with
    | some name => throw (.dirtyRegister name) | none => pure ()
    let pa ← liftInteger (Ptx.eval ctx.id.tid.x s.base.scalar.core.thread (.reg a))
    let pb ← liftInteger (Ptx.eval ctx.id.tid.x s.base.scalar.core.thread (.reg b))
    let scale ← liftInteger (Ptx.eval ctx.id.tid.x s.base.scalar.core.thread scaleD)
    let useD := scale != 0
    let input ← readScaledAccumulator s d scale
    let call := makeCall ctx s oracle d pa pb useD input
    pure (issueState s call,[.mma (mark ctx s) call])
  | other =>
    let touched := ordinaryNames other
    match touched.find? (fun name => (pendingNames s.ledger).contains name) with
    | some name => throw (.pendingRegister name) | none => pure ()
    let result ← liftBase (Hopper.step ctx oracle.base code s.base)
    pure ({base := result.1,ledger := {s.ledger with dirty := (touched++s.ledger.dirty).eraseDups}},result.2.map Event.base)

def run (ctx : Scalar.Context) (oracle : Oracle) (code : List Hopper.Instr) : Nat → State → Except Fault (State × List Event)
  | 0,s => .ok (s,[])
  | n+1,s => (step ctx oracle code s).bind fun first =>
      (run ctx oracle code n first.1).bind fun last => .ok (last.1,first.2++last.2)
def runLocated (ctx : Scalar.Context) (oracle : Oracle) (code : List Hopper.Instr) :=
  SourceRun.run (step ctx oracle code) (fun s => s.base.scalar.core.thread.pc)

def Complete (s : State) : Prop := s.base.scalar.core.thread.status = .done ∧ pending s.ledger = []

end
end Ptx.Hopper.Wgmma
