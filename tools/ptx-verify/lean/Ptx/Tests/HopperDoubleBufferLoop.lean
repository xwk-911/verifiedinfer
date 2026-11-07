import Ptx.Kernels.HopperDoubleBufferLoopSchedule
import Ptx.Kernels.HopperDoubleBufferLoopWitness
import Ptx.Tests.HopperDoubleBufferIteration

/-! Actual arbitrary-loop source examples plus independent schedule checks.
The runs start at the loop checkpoint, not a reconstructed initial kernel.
Only decidable metadata/fuel/query facts are evaluated. -/
namespace Ptx.HopperDoubleBufferLoopTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def seed (tiles : Nat) (leader : Bool) : Wgmma.State :=
  let old := Ptx.HopperDoubleBufferIterationTests.seed 0 tiles leader
  {old with base := {old.base with scalar := {old.base.scalar with
    core := {old.base.scalar.core with queries := if leader then 4 else 0}
    floats := Ptx.Kernels.HopperStage.zeroFloats}}}
def source (tiles : Nat) (leader : Bool) :=
  (Wgmma.run (ctx tiles (if leader then 0 else 127)) (oracle tiles) code
    (loopFuel 0 tiles leader zeroRetries tiles) (seed tiles leader)).toOption
structure Metadata where
  pc : Nat
  query : Nat
  groups : Nat
  completed : Nat
  pending : Nat
  calls : Nat
  tile : Option Nat
  slot : Option Nat
  phase0 : Option Nat
  phase1 : Option Nat
  deriving DecidableEq

def metadata (tiles : Nat) (leader : Bool) : Option Metadata :=
  (source tiles leader).map fun r => ⟨r.1.base.scalar.core.thread.pc,r.1.base.scalar.core.queries,
    r.1.ledger.groups,r.1.ledger.completed,(Wgmma.pending r.1.ledger).length,r.1.ledger.calls.length,
    lookup "%tile" r.1.base.scalar.core.thread.regs,lookup "%slot" r.1.base.scalar.core.thread.regs,
    lookup "%phase0" r.1.base.scalar.core.thread.regs,lookup "%phase1" r.1.base.scalar.core.thread.regs⟩
def transferQueries (tiles : Nat) (leader : Bool) :=
  (source tiles leader).map fun r => r.2.filterMap Ptx.HopperDoubleBufferIterationTests.queryMetadata

theorem producer_six_tiles : metadata 6 true = some ⟨85,42,6,6,0,6,some 6,some 0,some 1,some 1⟩ := by decide
theorem consumer_six_tiles : metadata 6 false = some ⟨85,18,6,6,0,6,some 6,some 0,some 1,some 1⟩ := by decide
theorem producer_seven_tiles : metadata 7 true = some ⟨85,49,7,7,0,7,some 7,some 1,some 0,some 1⟩ := by decide
theorem consumer_seven_tiles : metadata 7 false = some ⟨85,21,7,7,0,7,some 7,some 1,some 0,some 1⟩ := by decide
theorem all_prefetch_queries_retained : transferQueries 6 true = some [5,7,12,14,19,21,26,28,33,35] := by decide
theorem consumer_never_prefetches : transferQueries 6 false = some [] := by decide

def varyingRetries (tile : Nat) : Nat := tile%3

theorem full_producer_schedule_with_retries : loopQuery 0 7 true varyingRetries 4 7 = 55 := by decide
theorem full_consumer_schedule_with_retries : loopQuery 0 7 false varyingRetries 0 7 = 27 := by decide
theorem retry_count_is_six : loopRetryCount 0 varyingRetries 7 = 6 := by decide
theorem producer_prefetch_count_is_six : loopPrefetchCount 0 7 true 7 = 6 := by decide
theorem consumer_prefetch_count_is_zero : loopPrefetchCount 0 7 false 7 = 0 := by decide
theorem six_tile_producer_fuel : loopFuel 0 6 true zeroRetries 6 = 198 := by decide
theorem six_tile_consumer_fuel : loopFuel 0 6 false zeroRetries 6 = 152 := by decide

end
end Ptx.HopperDoubleBufferLoopTests
