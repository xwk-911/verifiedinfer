import Ptx.Kernels.HopperDoubleBufferContext
import Ptx.Hopper.UnifiedSource

/-! Actual generated-source probes for T=0,1,2,3,4,5 in the producer and last
consumer lanes, with successful waits and zero-valued matrix replies. These
are finite source/completion checks, not full launch consistency, arbitrary-T
execution or functional correctness. The independent specification is separate.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def probeLane (who : Fin 2) : Wgmma.Lane := if who.val = 0 then 0 else 127
def probeCount (tiles : Fin 6) (who : Fin 2) : Nat :=
  if tiles.val = 0 then (if who.val = 0 then 51 else 46)
  else if who.val = 0 then 35*tiles.val+49 else 50+24*tiles.val+3*(tiles.val/2)
def probeResult (tiles : Fin 6) (who : Fin 2) : Wgmma.State × List Wgmma.Event :=
  (Wgmma.run (ctx tiles.val (probeLane who)) (oracle tiles.val) Generated.hopper_double_buffer_gemm.program (probeCount tiles who) {}).toOption.getD ({},[])
def probeTrace (tiles : Fin 6) (who : Fin 2) : Unified.ThreadTrace :=
  ⟨(ctx tiles.val (probeLane who)).id,oracle tiles.val,probeCount tiles who,(probeResult tiles who).1,(probeResult tiles who).2⟩

theorem all_probes_succeed : ∀ tiles : Fin 6, ∀ who : Fin 2,
    (Wgmma.run (ctx tiles.val (probeLane who)) (oracle tiles.val) Generated.hopper_double_buffer_gemm.program (probeCount tiles who) {}).toOption.isSome = true := by decide
theorem all_probes_complete_metadata : ∀ tiles : Fin 6, ∀ who : Fin 2,
    (((probeResult tiles who).1.base.scalar.core.thread.status == .done) &&
      ((Wgmma.pending (probeResult tiles who).1.ledger).length == 0)) = true := by decide
theorem all_probes_groups_metadata : ∀ tiles : Fin 6, ∀ who : Fin 2,
    (probeResult tiles who).1.ledger.groups = tiles.val ∧ (probeResult tiles who).1.ledger.completed = tiles.val ∧
      (probeResult tiles who).1.ledger.calls.length = tiles.val := by decide
theorem probe_produced (tiles : Fin 6) (who : Fin 2) :
    Unified.Produced Generated.hopper_double_buffer_gemm.program (params tiles.val) HopperStage.block (probeTrace tiles who) := by
  change Wgmma.run (ctx tiles.val (probeLane who)) (oracle tiles.val) Generated.hopper_double_buffer_gemm.program (probeCount tiles who) {} = .ok (probeResult tiles who)
  cases hs : Wgmma.run (ctx tiles.val (probeLane who)) (oracle tiles.val) Generated.hopper_double_buffer_gemm.program (probeCount tiles who) {} with
  | error fault => have hh := all_probes_succeed tiles who; rw [hs] at hh; cases hh
  | ok value => simp only [probeResult,hs,Except.toOption,Option.getD_some]
theorem probe_complete (tiles : Fin 6) (who : Fin 2) : Wgmma.Complete (probeTrace tiles who).final :=
  Wgmma.complete_of_metadata _ (all_probes_complete_metadata tiles who)

end
end Ptx.Kernels.HopperDoubleBuffer
