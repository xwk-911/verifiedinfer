import Ptx.Ampere.Syntax
import Ptx.Scalar.Execution

/-! Source-local issue/group/wait traces. A copy records oracle-supplied bytes
with an independent operation identity; it does not emit a synchronous store
or update any heap at issue, commit, or wait. Completion constraints and memory
agreement belong to the augmented graph, separately from this interpreter. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

structure Copy where
  cache : CopyCache
  group : Nat
  src : Location
  dst : Location
  bytes : List Symbolic.Byte

structure MmaInputs where
  a : Fin 4 → PackedF16
  b : Fin 2 → PackedF16
  c : Fin 4 → ℝ
structure MmaCall where
  pc : Nat
  ordinal : Nat
  warp : Nat
  lane : Mma.Lane
  inputs : MmaInputs
  output : Fin 4 → ℝ

inductive Event
  | ordinary (kind : Scalar.Kind)
  | issue (ordinal : Nat) (operation : Copy)
  | commit (group : Nat)
  | wait (groups keep : Nat)
  | mmaEntry (call : MmaCall)
  | mmaReturn (call : MmaCall)

structure State where
  scalar : Scalar.State := {}
  copies : List Copy := []
  groups : Nat := 0
  packed : List (String × PackedF16) := []
  mmaCalls : Nat := 0

structure Oracle where
  scalar : Scalar.Oracle
  bytes : Nat → List Symbolic.Byte
  word32 : Nat → Word32 := fun _ => .integer 0
  matrix : Nat → Fin 4 → ℝ := fun _ _ => 0

inductive Fault
  | scalar (fault : Scalar.Fault)
  | invalidPC (pc : Nat)
  | blocked
  | copySize
  | payloadSize (query expected actual : Nat)
  | waitCount (keep : Nat)
  | packedRegister (name : String)
  | mmaDestinations
  deriving Repr, DecidableEq

def liftScalar (result : Except Scalar.Fault α) : Except Fault α :=
  match result with | .ok a => .ok a | .error fault => .error (.scalar fault)
def liftInteger (result : Except Ptx.Fault α) : Except Fault α :=
  match result with | .ok a => .ok a | .error fault => .error (.scalar (.integer fault))
def advance (s : State) : State :=
  {s with scalar := {s.scalar with core := {s.scalar.core with thread := Ptx.advance s.scalar.core.thread}}}

def scalarWritten : Scalar.Instr → Option String
  | .integer i => match i with
    | .mov _ dst _ | .param _ dst _ | .bin _ _ _ dst _ _ | .setp _ dst _ _ | .load _ dst _ => some dst
    | _ => none
  | .setpGt _ dst _ _ | .readSpecial dst _ | .atomAddU32 dst _ _ | .mov _ dst _ |
    .addRn _ dst _ _ | .subRn _ dst _ _ | .mulRn _ dst _ _ | .divRn _ dst _ _ |
    .max _ dst _ _ | .ex2Approx dst _ | .fmaRn _ dst _ _ _ | .load _ _ dst _ => some dst
  | .store .. => none
def finishScalar (s : State) (i : Scalar.Instr) (next : Scalar.State) : State :=
  {s with scalar := next,packed := match scalarWritten i with
    | none => s.packed
    | some dst => s.packed.filter (fun kv => kv.1 != dst)}
@[simp] theorem finishScalar_empty {s : State} (hp : s.packed = []) (i : Scalar.Instr) (next : Scalar.State) :
    finishScalar s i next = {s with scalar := next} := by
  unfold finishScalar
  cases scalarWritten i <;> simp [hp]

def wordAction (s : State) (dst : String) (value : Word32) : State :=
  match value with
  | .integer n => {s with
      scalar := Scalar.finishInteger s.scalar {s.scalar.core with
        thread := assign s.scalar.core.thread dst (wrap 32 n),queries := s.scalar.core.queries+1}
      packed := s.packed.filter (fun kv => kv.1 != dst)}
  | .packed pair =>
    let next := advance s
    {next with
      scalar := {next.scalar with
        core := {next.scalar.core with
          thread := {next.scalar.core.thread with regs := next.scalar.core.thread.regs.filter (fun kv => kv.1 != dst)}
          queries := s.scalar.core.queries+1}
        floats := next.scalar.floats.filter (fun kv => kv.1 != dst)}
      packed := (dst,pair) :: s.packed.filter (fun kv => kv.1 != dst)}

def requirePacked (s : State) (name : String) : Except Fault PackedF16 :=
  match declarationLookup name s.packed with | some value => .ok value | none => .error (.packedRegister name)
def readMmaInputs (s : State) (a : Registers4) (b : Registers2) (c : Registers4) : Except Fault MmaInputs := do
  let a0 ← requirePacked s a.r0
  let a1 ← requirePacked s a.r1
  let a2 ← requirePacked s a.r2
  let a3 ← requirePacked s a.r3
  let b0 ← requirePacked s b.r0
  let b1 ← requirePacked s b.r1
  let c0 ← liftScalar (Scalar.eval .f32 s.scalar (.reg c.r0))
  let c1 ← liftScalar (Scalar.eval .f32 s.scalar (.reg c.r1))
  let c2 ← liftScalar (Scalar.eval .f32 s.scalar (.reg c.r2))
  let c3 ← liftScalar (Scalar.eval .f32 s.scalar (.reg c.r3))
  return {
    a := fun i => if i.val = 0 then a0 else if i.val = 1 then a1 else if i.val = 2 then a2 else a3
    b := fun i => if i.val = 0 then b0 else b1
    c := fun i => if i.val = 0 then c0 else if i.val = 1 then c1 else if i.val = 2 then c2 else c3}

def linearThread (ctx : Scalar.Context) : Nat :=
  ctx.id.tid.x + ctx.block.x*(ctx.id.tid.y + ctx.block.y*ctx.id.tid.z)
def makeMmaCall (ctx : Scalar.Context) (s : State) (inputs : MmaInputs) (output : Fin 4 → ℝ) : MmaCall :=
  ⟨s.scalar.core.thread.pc,s.mmaCalls,linearThread ctx / 32,
    ⟨linearThread ctx % 32,Nat.mod_lt _ (by decide)⟩,inputs,output⟩
def mmaAction (s : State) (d : Registers4) (output : Fin 4 → ℝ) : State :=
  let next := advance s
  let core := {next.scalar.core with
    thread := {next.scalar.core.thread with regs := next.scalar.core.thread.regs.filter (fun kv => !d.names.contains kv.1)}
    queries := s.scalar.core.queries+1}
  let floats := [(d.r0,(.f32,output 0)),(d.r1,(.f32,output 1)),(d.r2,(.f32,output 2)),(d.r3,(.f32,output 3))] ++
    s.scalar.floats.filter (fun kv => !d.names.contains kv.1)
  {next with
    scalar := {core := core,floats := floats}
    packed := s.packed.filter (fun kv => !d.names.contains kv.1)
    mmaCalls := s.mmaCalls+1}

def issue (s : State) (op : Copy) : State × List Event :=
  let next := advance s
  let nextCore := {next.scalar.core with queries := s.scalar.core.queries+1}
  let nextScalar := {next.scalar with core := nextCore}
  ({next with scalar := nextScalar,copies := s.copies ++ [op]},[.issue s.copies.length op])

def step (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) (s : State) : Except Fault (State × List Event) := do
  if s.scalar.core.thread.status != .running then throw .blocked
  let instruction ← match code[s.scalar.core.thread.pc]? with
    | some i => .ok i
    | none => .error (.invalidPC s.scalar.core.thread.pc)
  match instruction with
  | .scalar i =>
    let result ← liftScalar (Scalar.step ctx oracle.scalar (scalarSkeleton code) s.scalar)
    return (finishScalar s i result.1,result.2.map Event.ordinary)
  | .copy cache dst src size =>
    if ¬ CopySize cache size then throw .copySize
    let srcAddr ← liftInteger (evalAddr ctx.id.tid.x s.scalar.core.thread src)
    let dstAddr ← liftInteger (evalAddr ctx.id.tid.x s.scalar.core.thread dst)
    let bytes := oracle.bytes s.scalar.core.queries
    if bytes.length != size then throw (.payloadSize s.scalar.core.queries size bytes.length)
    let op : Copy := ⟨cache,s.groups,⟨.global,srcAddr⟩,⟨.shared ctx.id.cta,dstAddr⟩,bytes⟩
    return issue s op
  | .commit => return ({advance s with groups := s.groups+1},[.commit s.groups])
  | .wait keep =>
    if keep ≥ 8 then throw (.waitCount keep)
    return (advance s,[.wait s.groups keep])
  | .waitAll =>
    return ({advance s with groups := s.groups+1},[.commit s.groups,.wait (s.groups+1) 0])
  | .loadWord32 space dst address =>
    let addr ← liftInteger (evalAddr ctx.id.tid.x s.scalar.core.thread address)
    let value := oracle.word32 s.scalar.core.queries
    return (wordAction s dst value,[.ordinary (.read (Location.resolve space ctx.id addr) value.encode)])
  | .mma d a b c =>
    if ¬ d.names.Nodup then throw .mmaDestinations
    let inputs ← readMmaInputs s a b c
    let output := oracle.matrix s.scalar.core.queries
    let call := makeMmaCall ctx s inputs output
    return (mmaAction s d output,[.mmaEntry call,.mmaReturn call])

def run (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) : Nat → State → Except Fault (State × List Event)
  | 0,s => .ok (s,[])
  | n+1,s => (step ctx oracle code s).bind fun head =>
      (run ctx oracle code n head.1).bind fun tail => .ok (tail.1,head.2 ++ tail.2)

inductive Runs (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) : State → List Event → State → Prop
  | nil (s) : Runs ctx oracle code s [] s
  | cons {s mid last first rest} : step ctx oracle code s = .ok (mid,first) →
      Runs ctx oracle code mid rest last → Runs ctx oracle code s (first++rest) last

theorem run_sound {ctx oracle code n s last events} (h : run ctx oracle code n s = .ok (last,events)) :
    Runs ctx oracle code s events last := by
  induction n generalizing s last events with
  | zero => cases Except.ok.inj h; exact .nil s
  | succ n ih =>
    cases hs : step ctx oracle code s with
    | error fault => simp [run,hs,Except.bind] at h
    | ok head =>
      cases ht : run ctx oracle code n head.1 with
      | error fault => simp [run,hs,ht,Except.bind] at h
      | ok tail =>
        have he : (tail.1,head.2++tail.2) = (last,events) := Except.ok.inj (by simpa only [run,hs,ht,Except.bind] using h)
        cases he
        exact .cons hs (ih ht)

theorem scalar_step {ctx oracle code s i next emitted}
    (hr : s.scalar.core.thread.status = .running) (hi : code[s.scalar.core.thread.pc]? = some (.scalar i))
    (hs : Scalar.step ctx oracle.scalar (scalarSkeleton code) s.scalar = .ok (next,emitted)) :
    step ctx oracle code s = .ok (finishScalar s i next,emitted.map Event.ordinary) := by
  simp [step,hr,hi,hs,liftScalar,bind,Except.bind,pure,Except.pure]

theorem word_step {ctx oracle code s space dst address addr}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.loadWord32 space dst address))
    (ha : evalAddr ctx.id.tid.x s.scalar.core.thread address = .ok addr) :
    step ctx oracle code s = .ok (wordAction s dst (oracle.word32 s.scalar.core.queries),
      [.ordinary (.read (Location.resolve space ctx.id addr) (oracle.word32 s.scalar.core.queries).encode)]) := by
  simp [step,hr,hi,ha,liftInteger,bind,Except.bind,pure,Except.pure]
theorem mma_step {ctx oracle code s d a b c inputs}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.mma d a b c)) (hd : d.names.Nodup)
    (hin : readMmaInputs s a b c = .ok inputs) :
    step ctx oracle code s = .ok (mmaAction s d (oracle.matrix s.scalar.core.queries),
      [.mmaEntry (makeMmaCall ctx s inputs (oracle.matrix s.scalar.core.queries)),
       .mmaReturn (makeMmaCall ctx s inputs (oracle.matrix s.scalar.core.queries))]) := by
  simp [step,hr,hi,hd,hin,bind,Except.bind,pure,Except.pure]

theorem commit_step {ctx oracle code s} (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some .commit) :
    step ctx oracle code s = .ok ({advance s with groups := s.groups+1},[.commit s.groups]) := by
  simp [step,hr,hi,bind,Except.bind,pure,Except.pure]
theorem wait_step {ctx oracle code s keep} (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.wait keep)) (hk : keep < 8) :
    step ctx oracle code s = .ok (advance s,[.wait s.groups keep]) := by
  simp [step,hr,hi,Nat.not_le_of_lt hk,bind,Except.bind,pure,Except.pure]
theorem wait_all_step {ctx oracle code s} (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some .waitAll) :
    step ctx oracle code s = .ok ({advance s with groups := s.groups+1},[.commit s.groups,.wait (s.groups+1) 0]) := by
  simp [step,hr,hi,bind,Except.bind,pure,Except.pure]

end
end Ptx.Ampere
