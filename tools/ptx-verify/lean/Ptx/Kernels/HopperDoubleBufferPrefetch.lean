import Ptx.Kernels.HopperDoubleBufferPrefetchTransfer

/-! Producer prefetch from actual PC 65 to PC 76. The trace records actual
queries and reply payloads, rather than assuming desired tensor values. These
source rules preserve current MMA operands and accumulators while preparing
the next buffer; visibility and resource histories remain separate obligations.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def prefetchState (s : Wgmma.State) (tile next : Nat) : Wgmma.State :=
  prefetchTransferState (prefetchAddressState s tile next)
def prefetchSteps (tile : Nat) : Nat := prefetchAddressSteps tile+3

theorem prefetch_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (tile next mapA mapB : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 65)
    (hp : Wgmma.pending s.ledger = [])
    (he : lookup "%even" s.base.scalar.core.thread.regs = some (if tile%2 = 0 then 1 else 0))
    (hb0 : lookup "%bar0" s.base.scalar.core.thread.regs = some 0)
    (hb1 : lookup "%bar1" s.base.scalar.core.thread.regs = some 8)
    (hn : lookup "%next" s.base.scalar.core.thread.regs = some next)
    (hma : lookup "%mapa" s.base.scalar.core.thread.regs = some mapA)
    (hmb : lookup "%mapb" s.base.scalar.core.thread.regs = some mapB)
    (hbound : next*8 < 2^32)
    (hshapeA : (oracle.base.tmaBytes (s.base.scalar.core.queries+1)).length = (oracle.base.descriptor s.base.scalar.core.queries).bytes)
    (hshapeB : (oracle.base.tmaBytes (s.base.scalar.core.queries+3)).length = (oracle.base.descriptor (s.base.scalar.core.queries+2)).bytes) :
    Wgmma.run ctx oracle code (prefetchSteps tile) s = .ok
      (prefetchState s tile next,prefetchTransferEvents ctx oracle s (stage (tile+1)) next mapA mapB) := by
  have haddr := prefetch_addresses_execute ctx oracle s tile next hr hpc hp he hb0 hb1 hn hbound
  obtain ⟨hbar,ha,hb,hay⟩ := prefetchAddressState_operands s tile next
  have htma := prefetch_transfers_execute ctx oracle (prefetchAddressState s tile next) (stage (tile+1)) next mapA mapB
    (by simpa using hr) (prefetchAddressState_pc s tile next) (by simpa using hp) hbar ha hb
    (by rwa [prefetchAddressState_nat_frame _ _ _ "%mapa" (by decide)])
    (by rwa [prefetchAddressState_nat_frame _ _ _ "%mapb" (by decide)]) hay
    (by rwa [prefetchAddressState_nat_frame _ _ _ "%next" (by decide)])
    (by simpa using hshapeA) (by simpa using hshapeB)
  rw [prefetchSteps,Wgmma.run_add,haddr]
  simp only [Except.bind,htma,List.nil_append,prefetchState]
  simp [prefetchTransferEvents,prefetchACopy,prefetchBCopy]

@[simp] theorem prefetchState_pc (s : Wgmma.State) (tile next : Nat) :
    (prefetchState s tile next).base.scalar.core.thread.pc = 76 := by simp [prefetchState]
@[simp] theorem prefetchState_queries (s : Wgmma.State) (tile next : Nat) :
    (prefetchState s tile next).base.scalar.core.queries = s.base.scalar.core.queries+4 := by simp [prefetchState]
@[simp] theorem prefetchState_status (s : Wgmma.State) (tile next : Nat) :
    (prefetchState s tile next).base.scalar.core.thread.status = s.base.scalar.core.thread.status := by simp [prefetchState]
@[simp] theorem prefetchState_pending (s : Wgmma.State) (tile next : Nat) :
    Wgmma.pending (prefetchState s tile next).ledger = Wgmma.pending s.ledger := by simp [prefetchState]

theorem prefetchState_nat_frame (s : Wgmma.State) (tile next : Nat) (name : String)
    (hn : name ∉ ["%nextbar","%copya","%copyb","%ay"]) :
    lookup name (prefetchState s tile next).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := by
  rw [prefetchState,prefetchTransferState_nat,prefetchAddressState_nat_frame _ _ _ _ hn]

theorem prefetchState_float_frame (s : Wgmma.State) (tile next : Nat) (name : String)
    (hx : name ∉ ["%nextbar","%copya","%copyb","%ay"]) (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (prefetchState s tile next).base.scalar.floats = declarationLookup name s.base.scalar.floats := by
  rw [prefetchState,prefetchTransferState_float,prefetchAddressState_float_frame _ _ _ _ hx hn]

@[simp] theorem prefetchState_groups (s : Wgmma.State) (tile next : Nat) :
    (prefetchState s tile next).ledger.groups = s.ledger.groups := by
  by_cases h : tile%2 = 0
  all_goals simp only [prefetchState,prefetchTransferState,prefetchAIssued,prefetchArrived,
    prefetchAddressState,prefetchSelected,prefetchAddressPrefix,h,ite_true,ite_false]
  all_goals rfl
@[simp] theorem prefetchState_completed (s : Wgmma.State) (tile next : Nat) :
    (prefetchState s tile next).ledger.completed = s.ledger.completed := by
  by_cases h : tile%2 = 0
  all_goals simp only [prefetchState,prefetchTransferState,prefetchAIssued,prefetchArrived,
    prefetchAddressState,prefetchSelected,prefetchAddressPrefix,h,ite_true,ite_false]
  all_goals rfl

end
end Ptx.Kernels.HopperDoubleBuffer
