import Std

deriving instance DecidableEq for Except

private def Option.toExcept (x : Option α) (error : ε) : Except ε α :=
  match x with
  | some value => .ok value
  | none => .error error

/-! Fixed, executable operational semantics for one CTA of the supported PTX subset.
Addresses are bytes; allocated memory is a list of aligned 32-bit cells. Uninitialized
registers and memory, out-of-bounds, misalignment and unordered conflicts are faults.
This conservative epoch race monitor is NOT a model of arbitrary PTX synchronization.
-/
namespace Ptx

@[simp] theorem option_toExcept_some (value : α) (error : ε) :
    (some value).toExcept error = .ok value := rfl
@[simp] theorem option_toExcept_none (error : ε) :
    (none : Option α).toExcept error = .error error := rfl

inductive Space | global | shared deriving Repr, DecidableEq, BEq
deriving instance ReflBEq, LawfulBEq for Space
inductive Operand | imm (n : Nat) | reg (r : String) | tid deriving Repr, DecidableEq
structure Address where
  base : Operand
  offset : Nat := 0
  deriving Repr, DecidableEq
inductive BinOp | add | sub | mul deriving Repr, DecidableEq
inductive Cmp | lt | ge | eq deriving Repr, DecidableEq
inductive Instr where
  | mov (width : Nat) (dst : String) (a : Operand)
  | param (width : Nat) (dst name : String)
  | bin (op : BinOp) (inputWidth outputWidth : Nat) (dst : String) (a b : Operand)
  | setp (cmp : Cmp) (dst : String) (a b : Operand)
  | load (space : Space) (dst : String) (addr : Address)
  | store (space : Space) (addr : Address) (value : Operand)
  | branch (pred : String) (positive : Bool) (target : Nat)
  | jump (target : Nat)
  | barrier (id : Nat)
  | ret
  deriving Repr, DecidableEq

inductive Fault where
  | register (name : String)
  | parameter (name : String)
  | bounds (space : Space) (address : Nat)
  | unaligned (address : Nat)
  | uninitialized (space : Space) (address : Nat)
  | race (space : Space) (address first second : Nat)
  | invalidPC (pc : Nat)
  | invalidThread (tid : Nat)
  | blocked
  | barrierMismatch
  | notLocal
  | fuel
  deriving Repr, DecidableEq

abbrev Bindings := List (String × Nat)
def lookup (r : String) : Bindings → Option Nat
  | [] => none
  | (k,v)::xs => if k == r then some v else lookup r xs
def put (r : String) (v : Nat) (xs : Bindings) : Bindings :=
  (r,v) :: xs.filter (fun kv => kv.1 != r)
def wrap (width n : Nat) : Nat := n % 2^width

inductive Status | running | waiting (barrier : Nat) | done deriving Repr, DecidableEq, BEq
deriving instance ReflBEq, LawfulBEq for Status
structure Thread where
  pc : Nat := 0
  regs : Bindings := []
  status : Status := .running
  deriving Repr, DecidableEq
structure Access where
  space : Space
  address : Nat
  thread : Nat
  write : Bool
  epoch : Nat
  deriving Repr, DecidableEq
structure Machine where
  threads : List Thread
  globalMem : List (Option Nat)
  sharedMem : List (Option Nat)
  params : Bindings := []
  epoch : Nat := 0
  history : List Access := []
  deriving Repr, DecidableEq

def eval (tid : Nat) (t : Thread) : Operand → Except Fault Nat
  | .imm n => .ok n
  | .tid => .ok tid
  | .reg r => (lookup r t.regs).toExcept (.register r)
def evalAddr (tid : Nat) (t : Thread) (a : Address) : Except Fault Nat := do
  return wrap 64 ((← eval tid t a.base) + a.offset)
def memory (m : Machine) : Space → List (Option Nat)
  | .global => m.globalMem
  | .shared => m.sharedMem
def setMemory (m : Machine) (space : Space) (xs : List (Option Nat)) : Machine :=
  match space with
  | .global => { m with globalMem := xs }
  | .shared => { m with sharedMem := xs }
def conflict (a b : Access) : Bool :=
  a.space == b.space && a.address == b.address && a.thread != b.thread &&
  a.epoch == b.epoch && (a.write || b.write)
def checkedAccess (m : Machine) (a : Access) : Except Fault Machine :=
  if a.address % 4 != 0 then .error (.unaligned a.address)
  else if a.address / 4 ≥ (memory m a.space).length then .error (.bounds a.space a.address)
  else match m.history.find? (conflict a) with
    | some b => .error (.race a.space a.address b.thread a.thread)
    | none => .ok { m with history := a :: m.history }

theorem checkedAccess_bounds {m a m'} (h : checkedAccess m a = .ok m') :
    a.address % 4 = 0 ∧ a.address / 4 < (memory m a.space).length := by
  unfold checkedAccess at h
  split at h
  · cases h
  · rename_i ha
    split at h
    · cases h
    · rename_i hb
      simp at ha
      exact ⟨ha, by omega⟩

theorem checkedAccess_no_conflict {m a m'} (h : checkedAccess m a = .ok m') :
    m.history.find? (conflict a) = none := by
  unfold checkedAccess at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h
  · cases h
  · assumption

def advance (t : Thread) : Thread := { t with pc := t.pc + 1 }
def assign (t : Thread) (r : String) (v : Nat) : Thread :=
  { advance t with regs := put r v t.regs }
def updateThread (m : Machine) (tid : Nat) (t : Thread) : Machine :=
  { m with threads := m.threads.set tid t }

/-- Thread-local instruction semantics, shared by the CTA interpreter and proof rules.
Memory instructions are handled only by threadStep, never approximated here. -/
def localStep (params : Bindings) (tid : Nat) (t : Thread) (i : Instr) : Except Fault Thread := do
  match i with
  | .mov w r a => return assign t r (wrap w (← eval tid t a))
  | .param w r p =>
    let v ← (lookup p params).toExcept (.parameter p)
    return assign t r (wrap w v)
  | .bin op iw ow r a b =>
    let x := wrap iw (← eval tid t a)
    let y := wrap iw (← eval tid t b)
    let v := match op with
      | .add => x + y
      | .sub => x + 2^iw - y
      | .mul => x * y
    return assign t r (wrap ow v)
  | .setp cmp r a b =>
    let x := wrap 32 (← eval tid t a)
    let y := wrap 32 (← eval tid t b)
    let p := match cmp with
      | .lt => decide (x < y)
      | .ge => decide (x ≥ y)
      | .eq => decide (x = y)
    return assign t r (if p then 1 else 0)
  | .branch r positive target =>
    let v ← (lookup r t.regs).toExcept (.register r)
    return { t with pc := if (v != 0) == positive then target else t.pc + 1 }
  | .jump target => return { t with pc := target }
  | .barrier id => return { advance t with status := .waiting id }
  | .ret => return { t with status := .done }
  | .load .. | .store .. => throw .notLocal

def isLocal : Instr → Bool
  | .load .. | .store .. => false
  | _ => true

/-- An arbitrary scheduler chooses a runnable thread. Waiting is a separate collective action. -/
def threadStep (code : List Instr) (tid : Nat) (m : Machine) : Except Fault Machine := do
  let t ← (m.threads[tid]?).toExcept (.invalidThread tid)
  if t.status != .running then throw .blocked
  let i ← (code[t.pc]?).toExcept (.invalidPC t.pc)
  match i with
  | .load space r a =>
    let addr ← evalAddr tid t a
    let m' ← checkedAccess m ⟨space, addr, tid, false, m.epoch⟩
    let v ← (((memory m' space)[addr / 4]?).bind id).toExcept (.uninitialized space addr)
    return updateThread m' tid (assign t r (wrap 32 v))
  | .store space a v =>
    let addr ← evalAddr tid t a
    let v := wrap 32 (← eval tid t v)
    let m' ← checkedAccess m ⟨space, addr, tid, true, m.epoch⟩
    return updateThread (setMemory m' space ((memory m' space).set (addr / 4) (some v))) tid (advance t)
  | i => return updateThread m tid (← localStep m.params tid t i)

/-- Full CTA rendezvous, including threads that might otherwise return early. No partial count. -/
def release (m : Machine) : Except Fault Machine := do
  let t ← m.threads.head?.toExcept .barrierMismatch
  match t.status with
  | .waiting id =>
    if m.threads.all (fun t => t.status == .waiting id) then
      return { m with threads := m.threads.map (fun t => { t with status := .running }), epoch := m.epoch + 1 }
    else throw .barrierMismatch
  | _ => throw .barrierMismatch

inductive Action | thread (tid : Nat) | release deriving Repr, DecidableEq
def step (code : List Instr) : Action → Machine → Except Fault Machine
  | .thread tid, m => threadStep code tid m
  | .release, m => release m
def run (code : List Instr) : List Action → Machine → Except Fault Machine
  | [], m => .ok m
  | a::as, m => (step code a m).bind (run code as)

/-- Relational semantics uses the same fixed step function; errors cannot be proof steps. -/
inductive Steps (code : List Instr) : Machine → Machine → Prop
  | refl (m) : Steps code m m
  | next {m m' m''} (a) : step code a m = .ok m' → Steps code m' m'' → Steps code m m''

theorem run_sound {code actions m m'} (h : run code actions m = .ok m') : Steps code m m' := by
  induction actions generalizing m with
  | nil => simp [run] at h; subst m'; exact .refl m
  | cons a actions ih =>
    simp only [run] at h
    cases hs : step code a m with
    | error e => simp [hs, Except.bind] at h
    | ok mid => exact .next a hs (ih (by simpa [hs, Except.bind] using h))

end Ptx
