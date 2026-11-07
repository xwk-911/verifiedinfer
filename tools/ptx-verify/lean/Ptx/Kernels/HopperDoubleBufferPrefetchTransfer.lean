import Ptx.Kernels.HopperDoubleBufferPrefetchAddresses

/-! Actual PCs 73..75: expectation and A/B TMA issues at the caller's current
query counter. Only source-required payload lengths are premises. Descriptors,
bytes and copies are retained verbatim for later tensor/resource admission.
Issue is not completion and does not update a heap in the source interpreter.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def prefetchArrive : Hopper.Instr := .arriveExpectTx ⟨.reg "%nextbar",0⟩ (.imm 2304)
def prefetchAInstruction : Hopper.Instr :=
  .tmaLoad2D ⟨.reg "%copya",0⟩ (.reg "%mapa") (.imm 0) (.reg "%ay") ⟨.reg "%nextbar",0⟩
def prefetchBInstruction : Hopper.Instr :=
  .tmaLoad2D ⟨.reg "%copyb",0⟩ (.reg "%mapb") (.imm 0) (.reg "%next") ⟨.reg "%nextbar",0⟩
def prefetchArrived (s : Wgmma.State) : Wgmma.State := Wgmma.advanceOrdinary s prefetchArrive
def prefetchAIssued (s : Wgmma.State) : Wgmma.State := Wgmma.tmaState (prefetchArrived s) prefetchAInstruction
def prefetchTransferState (s : Wgmma.State) : Wgmma.State := Wgmma.tmaState (prefetchAIssued s) prefetchBInstruction

def prefetchACopy (oracle : Wgmma.Oracle) (s : Wgmma.State) (slot : Stage) (next mapA : Nat) : TmaCopy :=
  ⟨wrap 64 mapA,oracle.base.descriptor s.base.scalar.core.queries,⟨0,Tma.signed32 (8*next)⟩,
   aBase slot,barrierAddress slot,s.base.scalar.core.queries,oracle.base.tmaBytes (s.base.scalar.core.queries+1)⟩
def prefetchBCopy (oracle : Wgmma.Oracle) (s : Wgmma.State) (slot : Stage) (next mapB : Nat) : TmaCopy :=
  ⟨wrap 64 mapB,oracle.base.descriptor (s.base.scalar.core.queries+2),⟨0,Tma.signed32 next⟩,
   bBase slot,barrierAddress slot,s.base.scalar.core.queries+2,oracle.base.tmaBytes (s.base.scalar.core.queries+3)⟩
def prefetchTransferEvents (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (slot : Stage) (next mapA mapB : Nat) : List Wgmma.Event :=
  [.base (.barrier ⟨⟨.shared ctx.id.cta,barrierAddress slot⟩,.arriveExpectTx 2304⟩),
   .base (.tmaIssue (prefetchACopy oracle s slot next mapA)),
   .base (.tmaIssue (prefetchBCopy oracle s slot next mapB))]

theorem eval_register_address (ctx : Scalar.Context) (s : Wgmma.State) (name : String) (value : Nat)
    (he : lookup name s.base.scalar.core.thread.regs = some value) (hb : value < 2^64) :
    evalAddr ctx.id.tid.x s.base.scalar.core.thread ⟨.reg name,0⟩ = .ok value := by
  have hw : value % 18446744073709551616 = value := Nat.mod_eq_of_lt hb
  simp [evalAddr,Ptx.eval,he,wrap,hw,bind,Except.bind,pure,Except.pure]

theorem prefetch_transfers_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (slot : Stage) (next mapA mapB : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 73)
    (hp : Wgmma.pending s.ledger = [])
    (hbar : lookup "%nextbar" s.base.scalar.core.thread.regs = some (barrierAddress slot))
    (ha : lookup "%copya" s.base.scalar.core.thread.regs = some (aBase slot))
    (hb : lookup "%copyb" s.base.scalar.core.thread.regs = some (bBase slot))
    (hma : lookup "%mapa" s.base.scalar.core.thread.regs = some mapA)
    (hmb : lookup "%mapb" s.base.scalar.core.thread.regs = some mapB)
    (hay : lookup "%ay" s.base.scalar.core.thread.regs = some (8*next))
    (hn : lookup "%next" s.base.scalar.core.thread.regs = some next)
    (hshapeA : (oracle.base.tmaBytes (s.base.scalar.core.queries+1)).length = (oracle.base.descriptor s.base.scalar.core.queries).bytes)
    (hshapeB : (oracle.base.tmaBytes (s.base.scalar.core.queries+3)).length = (oracle.base.descriptor (s.base.scalar.core.queries+2)).bytes) :
    Wgmma.run ctx oracle code 3 s = .ok (prefetchTransferState s,prefetchTransferEvents ctx oracle s slot next mapA mapB) := by
  have hslot := slot.isLt
  have hbarBound : barrierAddress slot < 2^64 := by dsimp [barrierAddress]; omega
  have haBound : aBase slot < 2^64 := by dsimp [aBase]; omega
  have hbBound : bBase slot < 2^64 := by dsimp [bBase]; omega
  have h0 : Wgmma.step ctx oracle code s = .ok
      (prefetchArrived s,[.base (.barrier ⟨⟨.shared ctx.id.cta,barrierAddress slot⟩,.arriveExpectTx 2304⟩)]) := by
    exact Wgmma.arrive_expect_step (ctx := ctx) (oracle := oracle) (code := code) (count := .imm 2304) hr
      (by simp [hpc,code,Generated.hopper_double_buffer_gemm.program]) hp
      (eval_register_address ctx s "%nextbar" _ hbar hbarBound) rfl
  have h1 : Wgmma.step ctx oracle code (prefetchArrived s) = .ok
      (prefetchAIssued s,[.base (.tmaIssue (prefetchACopy oracle s slot next mapA))]) := by
    have hh := Wgmma.tma_issue_step (ctx := ctx) (oracle := oracle)
      (s := prefetchArrived s) (dstAddr := aBase slot) (descriptorAddr := mapA)
      (px := 0) (py := 8*next) (barrierAddr := barrierAddress slot)
      (by simpa [prefetchArrived] using hr)
      (show code[(prefetchArrived s).base.scalar.core.thread.pc]? = some prefetchAInstruction by simp [prefetchArrived,hpc,prefetchAInstruction,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [prefetchArrived] using hp)
      (eval_register_address ctx (prefetchArrived s) "%copya" _ (by simpa [prefetchArrived] using ha) haBound)
      (by simp [Ptx.eval,prefetchArrived,hma]) rfl (by simp [Ptx.eval,prefetchArrived,hay])
      (eval_register_address ctx (prefetchArrived s) "%nextbar" _ (by simpa [prefetchArrived] using hbar) hbarBound)
      (by simpa [prefetchArrived] using hshapeA)
    simpa [prefetchAIssued,prefetchACopy,prefetchArrived,prefetchAInstruction,show Tma.signed32 0 = 0 from by decide] using hh
  have h2 : Wgmma.step ctx oracle code (prefetchAIssued s) = .ok
      (prefetchTransferState s,[.base (.tmaIssue (prefetchBCopy oracle s slot next mapB))]) := by
    have hh := Wgmma.tma_issue_step (ctx := ctx) (oracle := oracle)
      (s := prefetchAIssued s) (dstAddr := bBase slot) (descriptorAddr := mapB)
      (px := 0) (py := next) (barrierAddr := barrierAddress slot)
      (by simpa [prefetchAIssued,prefetchArrived] using hr)
      (show code[(prefetchAIssued s).base.scalar.core.thread.pc]? = some prefetchBInstruction by simp [prefetchAIssued,prefetchArrived,hpc,prefetchBInstruction,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [prefetchAIssued,prefetchArrived] using hp)
      (eval_register_address ctx (prefetchAIssued s) "%copyb" _ (by simpa [prefetchAIssued,prefetchArrived] using hb) hbBound)
      (by simp [Ptx.eval,prefetchAIssued,prefetchArrived,hmb]) rfl (by simp [Ptx.eval,prefetchAIssued,prefetchArrived,hn])
      (eval_register_address ctx (prefetchAIssued s) "%nextbar" _ (by simpa [prefetchAIssued,prefetchArrived] using hbar) hbarBound)
      (by simpa [prefetchAIssued,prefetchArrived,Nat.add_assoc] using hshapeB)
    simpa [prefetchTransferState,prefetchBCopy,prefetchAIssued,prefetchArrived,prefetchBInstruction,Nat.add_assoc,show Tma.signed32 0 = 0 from by decide] using hh
  simp only [Wgmma.run,h0,h1,h2,Except.bind,List.nil_append,List.cons_append,List.append_nil,prefetchTransferEvents]

@[simp] theorem prefetchTransferState_pc (s : Wgmma.State) :
    (prefetchTransferState s).base.scalar.core.thread.pc = s.base.scalar.core.thread.pc+3 := rfl
@[simp] theorem prefetchTransferState_queries (s : Wgmma.State) :
    (prefetchTransferState s).base.scalar.core.queries = s.base.scalar.core.queries+4 := rfl
@[simp] theorem prefetchTransferState_status (s : Wgmma.State) :
    (prefetchTransferState s).base.scalar.core.thread.status = s.base.scalar.core.thread.status := rfl
@[simp] theorem prefetchTransferState_pending (s : Wgmma.State) :
    Wgmma.pending (prefetchTransferState s).ledger = Wgmma.pending s.ledger := rfl
@[simp] theorem prefetchTransferState_nat (s : Wgmma.State) (name : String) :
    lookup name (prefetchTransferState s).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := rfl
@[simp] theorem prefetchTransferState_float (s : Wgmma.State) (name : String) :
    declarationLookup name (prefetchTransferState s).base.scalar.floats = declarationLookup name s.base.scalar.floats := rfl

theorem prefetch_copy_queries (oracle : Wgmma.Oracle) (s : Wgmma.State) (slot : Stage) (next mapA mapB : Nat) :
    (prefetchACopy oracle s slot next mapA).queryBase = s.base.scalar.core.queries ∧
    (prefetchBCopy oracle s slot next mapB).queryBase = s.base.scalar.core.queries+2 := ⟨rfl,rfl⟩
theorem prefetch_copy_coordinates (oracle : Wgmma.Oracle) (s : Wgmma.State) (slot : Stage) (next mapA mapB : Nat)
    (hsmall : 8*next < 2^31) :
    (prefetchACopy oracle s slot next mapA).coordinates = ⟨0,(8*next : Nat)⟩ ∧
    (prefetchBCopy oracle s slot next mapB).coordinates = ⟨0,(next : Nat)⟩ := by
  simp [prefetchACopy,prefetchBCopy,Tma.signed32_of_small hsmall,Tma.signed32_of_small (show next < 2^31 by omega)]

end
end Ptx.Kernels.HopperDoubleBuffer
