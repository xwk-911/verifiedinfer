import Ptx.Kernels.HopperDoubleBufferLoop
import Ptx.Kernels.HopperDoubleBufferContext

/-! A constructed, arbitrary-length source witness with represented zero
inputs and successful waits, from an explicit loop-entry invariant. This is
source nonvacuity only, not a resource/memory-admitted completed launch. The
generic loop theorem separately supports arbitrary finite per-tile retries. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def zeroRetries : Nat → Nat := fun _ => 0

theorem oracle_loop_replies (tiles query tile : Nat) (leader : Bool) :
    LoopReplies (oracle tiles) query tile tiles 0 leader := by
  refine ⟨by intro i hi; omega,by rfl,?_⟩
  intro _
  exact ⟨oracle_payload_shape tiles (query+1),by simpa [Nat.add_assoc] using oracle_payload_shape tiles (query+3)⟩

theorem zero_retry_loop_source (context : Scalar.Context) (first tiles : Nat) (leader : Bool)
    (s : Wgmma.State) (values : Fin 4 → ℝ) (mapA mapB : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s first tiles leader mapA mapB) (hacc : Accumulators s values)
    (hfirst : first < tiles) (hbound : tiles ≤ 2^28) :
    Wgmma.run context (oracle tiles) code (loopFuel first tiles leader zeroRetries (tiles-first)) s = .ok
      ((loopCheckpoint context (oracle tiles) first tiles leader zeroRetries s values (tiles-first)).1,
       loopEvents context (oracle tiles) first tiles leader zeroRetries s values mapA mapB (tiles-first)) := by
  apply loop_execute context (oracle tiles) first tiles leader zeroRetries s values mapA mapB
    hr hpc hp hc hregs hacc hfirst hbound (tiles-first) (by omega)
  intro i _
  exact oracle_loop_replies tiles _ _ leader

theorem zero_retry_loop_output (context : Scalar.Context) (first tiles : Nat) (leader : Bool)
    (s : Wgmma.State) (values : Fin 4 → ℝ) (mapA mapB : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s first tiles leader mapA mapB) (hacc : Accumulators s values)
    (hfirst : first < tiles) :
    (loopCheckpoint context (oracle tiles) first tiles leader zeroRetries s values (tiles-first)).1.base.scalar.core.thread.pc = 85 ∧
    Wgmma.pending (loopCheckpoint context (oracle tiles) first tiles leader zeroRetries s values (tiles-first)).1.ledger = [] :=
  full_loop_reaches_output context (oracle tiles) first tiles leader zeroRetries s values mapA mapB hr hpc hp hc hregs hacc hfirst

end
end Ptx.Kernels.HopperDoubleBuffer
