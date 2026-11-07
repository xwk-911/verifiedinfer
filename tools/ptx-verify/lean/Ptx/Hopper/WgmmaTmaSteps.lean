import Ptx.Hopper.WgmmaControl
import Ptx.Hopper.TmaSource

/-! TMA and transaction-expectation execution in the WGMMA interpreter.
Replies remain explicit source data. Neither issue nor arrive grants completed
bytes, proxy publication, operand agreement or a memory/resource admission. -/
namespace Ptx.Hopper.Wgmma
open Ptx.ISA
noncomputable section

theorem mul_const_step {ctx oracle code s dst src value factor}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.bin .mul 32 32 dst (.reg src) (.imm factor))))))
    (hp : pending s.ledger = []) (he : lookup src s.base.scalar.core.thread.regs = some value)
    (hv : value < 2^32) (hf : factor < 2^32) (hm : value*factor < 2^32) :
    step ctx oracle code s = .ok
      (integerAssign s (.bin .mul 32 32 dst (.reg src) (.imm factor)) dst (value*factor),[]) := by
  apply integer_assign_step hr hi hp rfl (by intro bid he; cases he) rfl
  have hwv : wrap 32 value = value := Nat.mod_eq_of_lt hv
  have hwf : wrap 32 factor = factor := Nat.mod_eq_of_lt hf
  have hwm : wrap 32 (value*factor) = value*factor := Nat.mod_eq_of_lt hm
  simp [localStep,Ptx.eval,he,bind,Except.bind,pure,Except.pure,hwv,hwf,hwm]

def advanceOrdinary (s : State) (instruction : Hopper.Instr) : State :=
  ordinaryState s instruction (Ampere.advance s.base)
def tmaState (s : State) (instruction : Hopper.Instr) : State :=
  let advanced := Ampere.advance s.base
  ordinaryState s instruction {advanced with scalar := {advanced.scalar with core := {advanced.scalar.core with queries := s.base.scalar.core.queries+2}}}

theorem arrive_expect_step {ctx oracle code s address count addr n}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.arriveExpectTx address count))
    (hp : pending s.ledger = [])
    (ha : evalAddr ctx.id.tid.x s.base.scalar.core.thread address = .ok addr)
    (hn : Ptx.eval ctx.id.tid.x s.base.scalar.core.thread count = .ok n) :
    step ctx oracle code s = .ok (advanceOrdinary s (.arriveExpectTx address count),
      [.base (.barrier ⟨⟨.shared ctx.id.cta,addr⟩,.arriveExpectTx (wrap 32 n)⟩)]) := by
  have hh := Hopper.arrive_expect_step (oracle := oracle.base) hr hi ha hn
  simpa [advanceOrdinary,ordinaryState] using ordinary_step hr hi (by intro wg he; cases he)
    (no_pending_names hp _) hh

theorem tma_issue_step {ctx oracle code s dst descriptor x y barrier dstAddr descriptorAddr px py barrierAddr}
    (hr : s.base.scalar.core.thread.status = .running)
    (hi : code[s.base.scalar.core.thread.pc]? = some (.tmaLoad2D dst descriptor x y barrier))
    (hp : pending s.ledger = [])
    (hd : evalAddr ctx.id.tid.x s.base.scalar.core.thread dst = .ok dstAddr)
    (hm : Ptx.eval ctx.id.tid.x s.base.scalar.core.thread descriptor = .ok descriptorAddr)
    (hx : Ptx.eval ctx.id.tid.x s.base.scalar.core.thread x = .ok px)
    (hy : Ptx.eval ctx.id.tid.x s.base.scalar.core.thread y = .ok py)
    (hb : evalAddr ctx.id.tid.x s.base.scalar.core.thread barrier = .ok barrierAddr)
    (hs : (oracle.base.tmaBytes (s.base.scalar.core.queries+1)).length = (oracle.base.descriptor s.base.scalar.core.queries).bytes) :
    step ctx oracle code s = .ok (tmaState s (.tmaLoad2D dst descriptor x y barrier),
      [.base (.tmaIssue ⟨wrap 64 descriptorAddr,oracle.base.descriptor s.base.scalar.core.queries,
        ⟨Tma.signed32 px,Tma.signed32 py⟩,dstAddr,barrierAddr,s.base.scalar.core.queries,
        oracle.base.tmaBytes (s.base.scalar.core.queries+1)⟩)]) := by
  have hh := Hopper.tma_step (oracle := oracle.base) hr hi hd hm hx hy hb hs
  simpa [tmaState,ordinaryState,Hopper.issueTma] using ordinary_step hr hi (by intro wg he; cases he)
    (no_pending_names hp _) hh

@[simp] theorem advanceOrdinary_pc (s : State) (instruction : Hopper.Instr) :
    (advanceOrdinary s instruction).base.scalar.core.thread.pc = s.base.scalar.core.thread.pc+1 := rfl
@[simp] theorem advanceOrdinary_status (s : State) (instruction : Hopper.Instr) :
    (advanceOrdinary s instruction).base.scalar.core.thread.status = s.base.scalar.core.thread.status := rfl
@[simp] theorem advanceOrdinary_queries (s : State) (instruction : Hopper.Instr) :
    (advanceOrdinary s instruction).base.scalar.core.queries = s.base.scalar.core.queries := rfl
@[simp] theorem advanceOrdinary_pending (s : State) (instruction : Hopper.Instr) :
    pending (advanceOrdinary s instruction).ledger = pending s.ledger := rfl
@[simp] theorem advanceOrdinary_nat (s : State) (instruction : Hopper.Instr) (name : String) :
    lookup name (advanceOrdinary s instruction).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := rfl
@[simp] theorem advanceOrdinary_float (s : State) (instruction : Hopper.Instr) (name : String) :
    declarationLookup name (advanceOrdinary s instruction).base.scalar.floats = declarationLookup name s.base.scalar.floats := rfl
@[simp] theorem tmaState_pc (s : State) (instruction : Hopper.Instr) :
    (tmaState s instruction).base.scalar.core.thread.pc = s.base.scalar.core.thread.pc+1 := rfl
@[simp] theorem tmaState_status (s : State) (instruction : Hopper.Instr) :
    (tmaState s instruction).base.scalar.core.thread.status = s.base.scalar.core.thread.status := rfl
@[simp] theorem tmaState_queries (s : State) (instruction : Hopper.Instr) :
    (tmaState s instruction).base.scalar.core.queries = s.base.scalar.core.queries+2 := rfl
@[simp] theorem tmaState_pending (s : State) (instruction : Hopper.Instr) :
    pending (tmaState s instruction).ledger = pending s.ledger := rfl
@[simp] theorem tmaState_nat (s : State) (instruction : Hopper.Instr) (name : String) :
    lookup name (tmaState s instruction).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := rfl
@[simp] theorem tmaState_float (s : State) (instruction : Hopper.Instr) (name : String) :
    declarationLookup name (tmaState s instruction).base.scalar.floats = declarationLookup name s.base.scalar.floats := rfl

theorem issue_preserves_wgmma_ledger (s : State) (instruction : Hopper.Instr) :
    (tmaState s instruction).ledger.groups = s.ledger.groups ∧
    (tmaState s instruction).ledger.completed = s.ledger.completed ∧
    (tmaState s instruction).ledger.calls = s.ledger.calls := ⟨rfl,rfl,rfl⟩

end
end Ptx.Hopper.Wgmma
