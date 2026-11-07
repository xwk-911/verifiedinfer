import Ptx.Kernels.HopperDoubleBufferReturn

/-! Composition of the real output/return suffix for arbitrary typed
accumulators and a completed local WGMMA ledger. Source completion is distinct
from launch admission and observable matrix correctness. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def outputState (s : Wgmma.State) (lane : Wgmma.Lane) (leader : Bool) : Wgmma.State :=
  returnedState (outputStored (outputAddressState s lane)) leader
def outputSteps (leader : Bool) : Nat := 7+4+returnSteps leader
def outputEvents (context : Scalar.Context) (s : Wgmma.State) (lane : Wgmma.Lane)
    (leader : Bool) (values : Fin 4 → ℝ) : List Wgmma.Event :=
  outputWriteEvents lane values++returnEvents context (outputStored (outputAddressState s lane)) leader

theorem output_execute (context : Scalar.Context) (reply : Wgmma.Oracle) (s : Wgmma.State)
    (lane : Wgmma.Lane) (leader : Bool) (values : Fin 4 → ℝ)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 85)
    (hp : Wgmma.pending s.ledger = [])
    (hx : lookup "%x" s.base.scalar.core.thread.regs = some (HopperStage.xWord lane))
    (hy : lookup "%y" s.base.scalar.core.thread.regs = some (HopperStage.yWord lane))
    (hz : lookup "%z" s.base.scalar.core.thread.regs = some (HopperStage.zWord lane))
    (hout : lookup "%out" s.base.scalar.core.thread.regs = some (wrap 64 8192))
    (hl : lookup "%leader" s.base.scalar.core.thread.regs = some (if leader then 1 else 0))
    (hb0 : lookup "%bar0" s.base.scalar.core.thread.regs = some 0)
    (hb1 : lookup "%bar1" s.base.scalar.core.thread.regs = some 8)
    (hacc : Accumulators s values) :
    Wgmma.run context reply code (outputSteps leader) s = .ok (outputState s lane leader,outputEvents context s lane leader values) := by
  have ha := output_addresses_execute context reply s lane hr hpc hp hx hy hz hout
  have hs := output_stores_execute context reply (outputAddressState s lane) lane values
    (by simpa using hr) (outputAddressState_pc s lane hpc) (by simpa using hp)
    (outputAddressState_out s lane) (outputAddressState_accumulators s lane values hacc)
  have hret := output_return_execute context reply (outputStored (outputAddressState s lane)) leader
    (by simpa using hr) (by simp [hpc]) (by simpa using hp)
    (by rwa [outputStored_nat,outputAddressState_nat_frame _ _ "%leader" (by decide)])
    (by rwa [outputStored_nat,outputAddressState_nat_frame _ _ "%bar0" (by decide)])
    (by rwa [outputStored_nat,outputAddressState_nat_frame _ _ "%bar1" (by decide)])
  rw [outputSteps,Wgmma.run_add,Wgmma.run_add,ha]
  simp only [Except.bind,hs,hret,List.nil_append,outputState,outputEvents]

theorem outputState_complete (s : Wgmma.State) (lane : Wgmma.Lane) (leader : Bool)
    (hp : Wgmma.pending s.ledger = []) : Wgmma.Complete (outputState s lane leader) := by
  apply returnedState_complete
  simpa using hp

@[simp] theorem outputState_queries (s : Wgmma.State) (lane : Wgmma.Lane) (leader : Bool) :
    (outputState s lane leader).base.scalar.core.queries = s.base.scalar.core.queries := by simp [outputState]
@[simp] theorem outputState_status (s : Wgmma.State) (lane : Wgmma.Lane) (leader : Bool) :
    (outputState s lane leader).base.scalar.core.thread.status = .done := by simp [outputState]
@[simp] theorem outputState_pending (s : Wgmma.State) (lane : Wgmma.Lane) (leader : Bool) :
    Wgmma.pending (outputState s lane leader).ledger = Wgmma.pending s.ledger := by simp [outputState]

theorem outputState_bookkeeping (s : Wgmma.State) (lane : Wgmma.Lane) (leader : Bool) :
    bookkeeping (outputState s lane leader) = bookkeeping s := by
  have hbar (st : Wgmma.State) : bookkeeping (Wgmma.barrierState st 1) = bookkeeping st := rfl
  have hret (st : Wgmma.State) : bookkeeping (Wgmma.returnState st) = bookkeeping st := rfl
  cases leader <;> simp only [outputState,returnedState,hret,outputStored,outputAddressState,
    hbar,integerPC_bookkeeping,integerAssign_bookkeeping,advanceOrdinary_bookkeeping,ite_true,ite_false,Bool.false_eq_true]

end
end Ptx.Kernels.HopperDoubleBuffer
