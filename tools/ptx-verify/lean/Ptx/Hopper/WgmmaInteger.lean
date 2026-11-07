import Ptx.Hopper.WgmmaRules
import Ptx.Ampere.ScalarSteps

/-! Integer execution through all three interpreter layers. The pending-call
condition is explicit; ordinary instructions retain their actual dirty names.
No arithmetic or memory reply is constrained by these lifting rules. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section

def ordinaryState (s : State) (instruction : Hopper.Instr) (next : Hopper.State) : State :=
  {base := next,ledger := {s.ledger with dirty := (ordinaryNames instruction++s.ledger.dirty).eraseDups}}
def integerAssign (s : State) (instruction : Ptx.Instr) (dst : String) (value : Nat) : State :=
  ordinaryState s (.ampere (.scalar (.integer instruction))) (Ampere.intAssign s.base dst value)
def integerPC (s : State) (instruction : Ptx.Instr) (pc : Nat) : State :=
  ordinaryState s (.ampere (.scalar (.integer instruction))) (Ampere.intPC s.base pc)

theorem no_pending_names {s : State} (hp : pending s.ledger = []) (instruction : Hopper.Instr) :
    (ordinaryNames instruction).find? (fun name => (pendingNames s.ledger).contains name) = none := by
  simp [pendingNames,hp]

theorem integer_local_step {ctx oracle code s instruction next}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer instruction))))
    (hp : pending s.ledger = [])
    (hl : isLocal instruction = true) (hb : ∀ bid, instruction ≠ .barrier bid)
    (hs : localStep ctx.params ctx.id.tid.x s.base.scalar.core.thread instruction = .ok next) :
    step ctx oracle code s = .ok
      (ordinaryState s (.ampere (.scalar (.integer instruction)))
        (Ampere.finishScalar s.base (.integer instruction)
          (Scalar.finishInteger s.base.scalar {s.base.scalar.core with thread := next})),[]) := by
  have ha := Ampere.integer_local_step (oracle := oracle.base.ampere) hr (Hopper.ampereSkeleton_slot hi) hl hb hs
  have hh := Hopper.embedded_step (oracle := oracle.base) hr hi ha
  simpa [ordinaryState] using ordinary_step hr hi (by intro wg he; cases he)
    (no_pending_names hp _) hh

theorem integer_assign_step {ctx oracle code s instruction dst value}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer instruction))))
    (hp : pending s.ledger = [])
    (hl : isLocal instruction = true) (hb : ∀ bid, instruction ≠ .barrier bid)
    (hw : Ampere.scalarWritten (.integer instruction) = some dst)
    (hs : localStep ctx.params ctx.id.tid.x s.base.scalar.core.thread instruction =
      .ok (assign s.base.scalar.core.thread dst value)) :
    step ctx oracle code s = .ok (integerAssign s instruction dst value,[]) := by
  simpa [integerAssign,Ampere.finishScalar,hw,Ampere.intAssign,Scalar.intAssign]
    using integer_local_step hr hi hp hl hb hs

theorem integer_pc_step {ctx oracle code s instruction pc}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer instruction))))
    (hp : pending s.ledger = [])
    (hl : isLocal instruction = true) (hb : ∀ bid, instruction ≠ .barrier bid)
    (hw : Ampere.scalarWritten (.integer instruction) = none)
    (hs : localStep ctx.params ctx.id.tid.x s.base.scalar.core.thread instruction =
      .ok {s.base.scalar.core.thread with pc := pc}) :
    step ctx oracle code s = .ok (integerPC s instruction pc,[]) := by
  simpa [integerPC,Ampere.finishScalar,hw,Ampere.intPC,Scalar.intPC]
    using integer_local_step hr hi hp hl hb hs

theorem mov_step {ctx oracle code s width dst operand value}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov width dst operand)))))
    (hp : pending s.ledger = [])
    (he : Ptx.eval ctx.id.tid.x s.base.scalar.core.thread operand = .ok value) :
    step ctx oracle code s = .ok (integerAssign s (.mov width dst operand) dst (wrap width value),[]) := by
  apply integer_assign_step hr hi hp rfl (by intro bid he; cases he) rfl
  simp [localStep,he,bind,Except.bind,pure,Except.pure]

theorem branch_step {ctx oracle code s name positive target value}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.branch name positive target)))))
    (hp : pending s.ledger = [])
    (he : lookup name s.base.scalar.core.thread.regs = some value) :
    step ctx oracle code s = .ok
      (integerPC s (.branch name positive target)
        (if (value != 0) == positive then target else s.base.scalar.core.thread.pc+1),[]) := by
  apply integer_pc_step hr hi hp rfl (by intro bid he; cases he) rfl
  simp [localStep,he,bind,Except.bind,pure,Except.pure]

theorem eq_zero_step {ctx oracle code s dst operand value}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.setp .eq dst operand (.imm 0))))))
    (hp : pending s.ledger = [])
    (he : Ptx.eval ctx.id.tid.x s.base.scalar.core.thread operand = .ok value)
    (hv : value < 2^32) :
    step ctx oracle code s = .ok
      (integerAssign s (.setp .eq dst operand (.imm 0)) dst (if value = 0 then 1 else 0),[]) := by
  apply integer_assign_step hr hi hp rfl (by intro bid he; cases he) rfl
  simp only [localStep,he,bind,Except.bind,pure,Except.pure]
  have hw : value % 4294967296 = value := Nat.mod_eq_of_lt hv
  simp [Ptx.eval,wrap,hw]

theorem flip_step {ctx oracle code s name value}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.bin .sub 32 32 name (.imm 1) (.reg name))))))
    (hp : pending s.ledger = [])
    (he : lookup name s.base.scalar.core.thread.regs = some value) (hv : value < 2) :
    step ctx oracle code s = .ok
      (integerAssign s (.bin .sub 32 32 name (.imm 1) (.reg name)) name (1-value),[]) := by
  apply integer_assign_step hr hi hp rfl (by intro bid he; cases he) rfl
  have h : value = 0 ∨ value = 1 := by omega
  rcases h with rfl | rfl <;>
    simp [localStep,Ptx.eval,he,wrap,bind,Except.bind,pure,Except.pure]

@[simp] theorem integerAssign_nat (s : State) (instruction : Ptx.Instr) (dst name : String) (value : Nat) :
    lookup name (integerAssign s instruction dst value).base.scalar.core.thread.regs =
      if name = dst then some value else lookup name s.base.scalar.core.thread.regs := by
  exact Ampere.intAssign_nat _ _ _ _
@[simp] theorem integerPC_nat (s : State) (instruction : Ptx.Instr) (pc : Nat) (name : String) :
    lookup name (integerPC s instruction pc).base.scalar.core.thread.regs =
      lookup name s.base.scalar.core.thread.regs := rfl
@[simp] theorem integerAssign_pc (s : State) (instruction : Ptx.Instr) (dst : String) (value : Nat) :
    (integerAssign s instruction dst value).base.scalar.core.thread.pc = s.base.scalar.core.thread.pc+1 := rfl
@[simp] theorem integerPC_pc (s : State) (instruction : Ptx.Instr) (pc : Nat) :
    (integerPC s instruction pc).base.scalar.core.thread.pc = pc := rfl
@[simp] theorem integerAssign_queries (s : State) (instruction : Ptx.Instr) (dst : String) (value : Nat) :
    (integerAssign s instruction dst value).base.scalar.core.queries = s.base.scalar.core.queries := rfl
@[simp] theorem integerPC_queries (s : State) (instruction : Ptx.Instr) (pc : Nat) :
    (integerPC s instruction pc).base.scalar.core.queries = s.base.scalar.core.queries := rfl
@[simp] theorem integerAssign_status (s : State) (instruction : Ptx.Instr) (dst : String) (value : Nat) :
    (integerAssign s instruction dst value).base.scalar.core.thread.status = s.base.scalar.core.thread.status := rfl
@[simp] theorem integerPC_status (s : State) (instruction : Ptx.Instr) (pc : Nat) :
    (integerPC s instruction pc).base.scalar.core.thread.status = s.base.scalar.core.thread.status := rfl
@[simp] theorem integerAssign_pending (s : State) (instruction : Ptx.Instr) (dst : String) (value : Nat) :
    pending (integerAssign s instruction dst value).ledger = pending s.ledger := rfl
@[simp] theorem integerPC_pending (s : State) (instruction : Ptx.Instr) (pc : Nat) :
    pending (integerPC s instruction pc).ledger = pending s.ledger := rfl

theorem integerAssign_float (s : State) (instruction : Ptx.Instr) (dst name : String) (value : Nat)
    (hd : name ≠ dst) (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (integerAssign s instruction dst value).base.scalar.floats =
      declarationLookup name s.base.scalar.floats := Ampere.intAssign_float _ _ _ _ hd hn
theorem integerPC_float (s : State) (instruction : Ptx.Instr) (pc : Nat) (name : String)
    (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (integerPC s instruction pc).base.scalar.floats =
      declarationLookup name s.base.scalar.floats := Ampere.intPC_float _ _ _ hn

end
end Ptx.Hopper.Wgmma
