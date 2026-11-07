import Ptx.Hopper.WgmmaInteger

/-! Bounded integer loop control and actual CTA barrier events inside the
WGMMA interpreter. A CTA barrier does not change group completion or pending
calls. Graph admission, not this local source rule, matches CTA participants. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section

theorem increment_step {ctx oracle code s dst src value}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.bin .add 32 32 dst (.reg src) (.imm 1))))))
    (hp : pending s.ledger = []) (he : lookup src s.base.scalar.core.thread.regs = some value)
    (hv : value+1 < 2^32) :
    step ctx oracle code s = .ok
      (integerAssign s (.bin .add 32 32 dst (.reg src) (.imm 1)) dst (value+1),[]) := by
  apply integer_assign_step hr hi hp rfl (by intro bid he; cases he) rfl
  have hw : wrap 32 value = value := Nat.mod_eq_of_lt (by omega)
  have hn : wrap 32 (value+1) = value+1 := Nat.mod_eq_of_lt hv
  simp [localStep,Ptx.eval,he,bind,Except.bind,pure,Except.pure,hw,hn,show wrap 32 1 = 1 from by decide]

theorem lt_step {ctx oracle code s dst left right x y}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.setp .lt dst (.reg left) (.reg right))))))
    (hp : pending s.ledger = [])
    (hx : lookup left s.base.scalar.core.thread.regs = some x)
    (hy : lookup right s.base.scalar.core.thread.regs = some y)
    (hxb : x < 2^32) (hyb : y < 2^32) :
    step ctx oracle code s = .ok
      (integerAssign s (.setp .lt dst (.reg left) (.reg right)) dst (if x < y then 1 else 0),[]) := by
  apply integer_assign_step hr hi hp rfl (by intro bid he; cases he) rfl
  have hwx : wrap 32 x = x := Nat.mod_eq_of_lt hxb
  have hwy : wrap 32 y = y := Nat.mod_eq_of_lt hyb
  simp [localStep,Ptx.eval,hx,hy,bind,Except.bind,pure,Except.pure,hwx,hwy]

def barrierState (s : State) (bid : Nat) : State :=
  ordinaryState s (.ampere (.scalar (.integer (.barrier bid)))) (Ampere.barrierState s.base bid)

theorem barrier_step {ctx oracle code s bid}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.barrier bid)))) ) :
    step ctx oracle code s = .ok (barrierState s bid,
      [.base (.ampere (.ordinary (.barrierArrival bid (Ptx.Event.generation s.base.scalar.core bid)))),
       .base (.ampere (.ordinary (.barrierReturn bid (Ptx.Event.generation s.base.scalar.core bid))))]) := by
  have ha := Ampere.barrier_step (ctx := ctx) (oracle := oracle.base.ampere) hr (Hopper.ampereSkeleton_slot hi)
  have hh := Hopper.embedded_step (oracle := oracle.base) hr hi ha
  simpa [barrierState,ordinaryState] using ordinary_step hr hi (by intro wg he; cases he)
    (by simp [ordinaryNames,ampereNames,scalarNames,integerNames]) hh

@[simp] theorem barrierState_pc (s : State) (bid : Nat) :
    (barrierState s bid).base.scalar.core.thread.pc = s.base.scalar.core.thread.pc+1 := rfl
@[simp] theorem barrierState_status (s : State) (bid : Nat) :
    (barrierState s bid).base.scalar.core.thread.status = s.base.scalar.core.thread.status := rfl
@[simp] theorem barrierState_queries (s : State) (bid : Nat) :
    (barrierState s bid).base.scalar.core.queries = s.base.scalar.core.queries := rfl
@[simp] theorem barrierState_pending (s : State) (bid : Nat) :
    pending (barrierState s bid).ledger = pending s.ledger := rfl
@[simp] theorem barrierState_nat (s : State) (bid : Nat) (name : String) :
    lookup name (barrierState s bid).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := rfl
@[simp] theorem barrierState_generation (s : State) (bid : Nat) :
    Ptx.Event.generation (barrierState s bid).base.scalar.core bid = Ptx.Event.generation s.base.scalar.core bid+1 :=
  Ampere.barrier_generation _ _
theorem barrierState_float (s : State) (bid : Nat) (name : String)
    (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (barrierState s bid).base.scalar.floats = declarationLookup name s.base.scalar.floats :=
  Ampere.barrier_float _ _ _ hn

theorem barrier_does_not_complete (s : State) (bid : Nat) :
    (barrierState s bid).ledger.completed = s.ledger.completed ∧
    (barrierState s bid).ledger.groups = s.ledger.groups ∧
    (barrierState s bid).ledger.calls = s.ledger.calls := ⟨rfl,rfl,rfl⟩

end
end Ptx.Hopper.Wgmma
