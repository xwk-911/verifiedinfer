import Ptx.Hopper.Syntax
import Ptx.Ampere.Updates
import Ptx.Event.SourceRun
import Ptx.Hopper.TmaDescriptor

/-! Source-local mbarrier, TMA issue and proxy-fence events. Wait, descriptor
and payload replies are oracle values. Actual phases, descriptor/input byte
agreement and completion belong to graph admission; issue mutates no heap.
Explicit complete_tx is a notification and does not perform a data transfer. -/
namespace Ptx.Hopper
open Ptx.ISA
noncomputable section

inductive BarrierOp
  | init (count : Nat)
  | inval
  | arriveExpectTx (count : Nat)
  | completeTx (count : Nat)
  | tryWaitParity (parity : Nat) (complete : Bool)
  deriving Repr, DecidableEq
structure BarrierEvent where
  location : Location
  operation : BarrierOp
  deriving Repr, DecidableEq
structure TmaCopy where
  descriptorAddress : Nat
  descriptor : Tma.Descriptor2D
  coordinates : Tma.Coordinates
  destination : Nat
  barrier : Nat
  queryBase : Nat
  payload : List Symbolic.Byte

inductive Event
  | ampere (kind : Ampere.Event)
  | tmaIssue (copy : TmaCopy)
  | proxyFenceAsyncShared (cta : Dim3)
  | barrier (event : BarrierEvent)
  | wgmma (tag : Wgmma.SourceTag)
abbrev State := Ampere.State
structure Oracle where
  ampere : Ampere.Oracle
  wait : Nat → Bool
  descriptor : Nat → Tma.Descriptor2D := fun _ => {}
  tmaBytes : Nat → List Symbolic.Byte := fun _ => []
inductive Fault
  | wgmmaExtensionRequired
  | ampere (fault : Ampere.Fault)
  | invalidPC (pc : Nat)
  | blocked
  | tmaPayloadSize (expected actual : Nat)
  deriving Repr, DecidableEq

def liftAmpere (result : Except Ampere.Fault α) : Except Fault α :=
  match result with | .ok a => .ok a | .error fault => .error (.ampere fault)
def liftInteger (result : Except Ptx.Fault α) : Except Fault α :=
  match result with | .ok a => .ok a | .error fault => .error (.ampere (.scalar (.integer fault)))
def waitState (s : State) (dst : String) (complete : Bool) : State :=
  let next := Ampere.intAssign s dst (if complete then 1 else 0)
  {next with scalar := {next.scalar with core := {next.scalar.core with queries := s.scalar.core.queries+1}}}

def issueTma (s : State) (copy : TmaCopy) : State × List Event :=
  let next := Ampere.advance s
  ({next with scalar := {next.scalar with core := {next.scalar.core with queries := s.scalar.core.queries+2}}},[.tmaIssue copy])

def step (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) (s : State) : Except Fault (State × List Event) := do
  if s.scalar.core.thread.status != .running then throw .blocked
  let instruction ← match code[s.scalar.core.thread.pc]? with
    | some i => .ok i
    | none => .error (.invalidPC s.scalar.core.thread.pc)
  match instruction with
  | .wgmma _ => throw .wgmmaExtensionRequired
  | .ampere _ =>
    let result ← liftAmpere (Ampere.step ctx oracle.ampere (ampereSkeleton code) s)
    return (result.1,result.2.map Event.ampere)
  | .proxyFenceAsyncShared => return (Ampere.advance s,[.proxyFenceAsyncShared ctx.id.cta])
  | .tmaLoad2D dst descriptor x y barrier =>
    let dstAddr ← liftInteger (evalAddr ctx.id.tid.x s.scalar.core.thread dst)
    let descriptorAddr ← liftInteger (Ptx.eval ctx.id.tid.x s.scalar.core.thread descriptor)
    let px ← liftInteger (Ptx.eval ctx.id.tid.x s.scalar.core.thread x)
    let py ← liftInteger (Ptx.eval ctx.id.tid.x s.scalar.core.thread y)
    let barrierAddr ← liftInteger (evalAddr ctx.id.tid.x s.scalar.core.thread barrier)
    let view := oracle.descriptor s.scalar.core.queries
    let payload := oracle.tmaBytes (s.scalar.core.queries+1)
    if payload.length != view.bytes then throw (.tmaPayloadSize view.bytes payload.length)
    return issueTma s ⟨wrap 64 descriptorAddr,view,⟨Tma.signed32 px,Tma.signed32 py⟩,dstAddr,barrierAddr,s.scalar.core.queries,payload⟩
  | .mbarrierInit address count =>
    let addr ← liftInteger (evalAddr ctx.id.tid.x s.scalar.core.thread address)
    let n ← liftInteger (Ptx.eval ctx.id.tid.x s.scalar.core.thread count)
    return (Ampere.advance s,[.barrier ⟨⟨.shared ctx.id.cta,addr⟩,.init (wrap 32 n)⟩])
  | .mbarrierInval address =>
    let addr ← liftInteger (evalAddr ctx.id.tid.x s.scalar.core.thread address)
    return (Ampere.advance s,[.barrier ⟨⟨.shared ctx.id.cta,addr⟩,.inval⟩])
  | .arriveExpectTx address count =>
    let addr ← liftInteger (evalAddr ctx.id.tid.x s.scalar.core.thread address)
    let n ← liftInteger (Ptx.eval ctx.id.tid.x s.scalar.core.thread count)
    return (Ampere.advance s,[.barrier ⟨⟨.shared ctx.id.cta,addr⟩,.arriveExpectTx (wrap 32 n)⟩])
  | .completeTx address count =>
    let addr ← liftInteger (evalAddr ctx.id.tid.x s.scalar.core.thread address)
    let n ← liftInteger (Ptx.eval ctx.id.tid.x s.scalar.core.thread count)
    return (Ampere.advance s,[.barrier ⟨⟨.shared ctx.id.cta,addr⟩,.completeTx (wrap 32 n)⟩])
  | .tryWaitParity dst address parity =>
    let addr ← liftInteger (evalAddr ctx.id.tid.x s.scalar.core.thread address)
    let p ← liftInteger (Ptx.eval ctx.id.tid.x s.scalar.core.thread parity)
    let answer := oracle.wait s.scalar.core.queries
    return (waitState s dst answer,[.barrier ⟨⟨.shared ctx.id.cta,addr⟩,.tryWaitParity (wrap 32 p) answer⟩])

def run (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) : Nat → State → Except Fault (State × List Event)
  | 0,s => .ok (s,[])
  | n+1,s => (step ctx oracle code s).bind fun first =>
      (run ctx oracle code n first.1).bind fun last => .ok (last.1,first.2++last.2)

def runLocated (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) :=
  SourceRun.run (step ctx oracle code) (fun s => s.scalar.core.thread.pc)

theorem run_eq_plain (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) (n : Nat) (s : State) :
    run ctx oracle code n s = SourceRun.plain (step ctx oracle code) n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [run,SourceRun.plain,ih]

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

@[simp] theorem waitState_pc (s : State) (dst : String) (complete : Bool) :
    (waitState s dst complete).scalar.core.thread.pc = s.scalar.core.thread.pc+1 := rfl
@[simp] theorem waitState_queries (s : State) (dst : String) (complete : Bool) :
    (waitState s dst complete).scalar.core.queries = s.scalar.core.queries+1 := rfl
@[simp] theorem waitState_result (s : State) (dst : String) (complete : Bool) :
    lookup dst (waitState s dst complete).scalar.core.thread.regs = some (if complete then 1 else 0) := by simp [waitState]

theorem embedded_step {ctx oracle code s i next events}
    (hr : s.scalar.core.thread.status = .running) (hi : code[s.scalar.core.thread.pc]? = some (.ampere i))
    (hs : Ampere.step ctx oracle.ampere (ampereSkeleton code) s = .ok (next,events)) :
    step ctx oracle code s = .ok (next,events.map Event.ampere) := by
  simp [step,hr,hi,hs,liftAmpere,bind,Except.bind,pure,Except.pure]

theorem init_step {ctx oracle code s address count addr n}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.mbarrierInit address count))
    (ha : evalAddr ctx.id.tid.x s.scalar.core.thread address = .ok addr)
    (hn : Ptx.eval ctx.id.tid.x s.scalar.core.thread count = .ok n) :
    step ctx oracle code s = .ok (Ampere.advance s,[.barrier ⟨⟨.shared ctx.id.cta,addr⟩,.init (wrap 32 n)⟩]) := by
  simp [step,hr,hi,ha,hn,liftInteger,bind,Except.bind,pure,Except.pure]

theorem inval_step {ctx oracle code s address addr}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.mbarrierInval address))
    (ha : evalAddr ctx.id.tid.x s.scalar.core.thread address = .ok addr) :
    step ctx oracle code s = .ok (Ampere.advance s,[.barrier ⟨⟨.shared ctx.id.cta,addr⟩,.inval⟩]) := by
  simp [step,hr,hi,ha,liftInteger,bind,Except.bind,pure,Except.pure]

theorem arrive_expect_step {ctx oracle code s address count addr n}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.arriveExpectTx address count))
    (ha : evalAddr ctx.id.tid.x s.scalar.core.thread address = .ok addr)
    (hn : Ptx.eval ctx.id.tid.x s.scalar.core.thread count = .ok n) :
    step ctx oracle code s = .ok (Ampere.advance s,[.barrier ⟨⟨.shared ctx.id.cta,addr⟩,.arriveExpectTx (wrap 32 n)⟩]) := by
  simp [step,hr,hi,ha,hn,liftInteger,bind,Except.bind,pure,Except.pure]

theorem complete_tx_step {ctx oracle code s address count addr n}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.completeTx address count))
    (ha : evalAddr ctx.id.tid.x s.scalar.core.thread address = .ok addr)
    (hn : Ptx.eval ctx.id.tid.x s.scalar.core.thread count = .ok n) :
    step ctx oracle code s = .ok (Ampere.advance s,[.barrier ⟨⟨.shared ctx.id.cta,addr⟩,.completeTx (wrap 32 n)⟩]) := by
  simp [step,hr,hi,ha,hn,liftInteger,bind,Except.bind,pure,Except.pure]

theorem try_wait_step {ctx oracle code s dst address parity addr p}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.tryWaitParity dst address parity))
    (ha : evalAddr ctx.id.tid.x s.scalar.core.thread address = .ok addr)
    (hp : Ptx.eval ctx.id.tid.x s.scalar.core.thread parity = .ok p) :
    step ctx oracle code s = .ok (waitState s dst (oracle.wait s.scalar.core.queries),
      [.barrier ⟨⟨.shared ctx.id.cta,addr⟩,.tryWaitParity (wrap 32 p) (oracle.wait s.scalar.core.queries)⟩]) := by
  simp [step,hr,hi,ha,hp,liftInteger,bind,Except.bind,pure,Except.pure]

end
end Ptx.Hopper
