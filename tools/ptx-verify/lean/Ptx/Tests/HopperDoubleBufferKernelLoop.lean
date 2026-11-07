import Ptx.Kernels.HopperDoubleBufferKernelLoop
import Ptx.Tests.HopperDoubleBufferLoop

/-! Runs of the actual kernel from empty state to output entry, extending
finite earlier probes. Output stores/return and graph admission remain open.
Every evaluated proposition compares closed decidable metadata only. -/
namespace Ptx.HopperDoubleBufferKernelLoopTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def source (tiles : Nat) (lane : Wgmma.Lane) :=
  (Wgmma.run (ctx tiles lane) (oracle tiles) code
    (if tiles = 0 then zeroTileSteps lane else kernelLoopSteps tiles lane) {}).toOption
structure Metadata where
  pc : Nat
  query : Nat
  groups : Nat
  completed : Nat
  pending : Nat
  calls : Nat
  done : Bool
  tile : Option Nat
  output : Option Nat
  x : Option Nat
  y : Option Nat
  z : Option Nat
  leader : Option Nat
  deriving DecidableEq

def metadata (tiles : Nat) (lane : Wgmma.Lane) : Option Metadata :=
  (source tiles lane).map fun r => ⟨r.1.base.scalar.core.thread.pc,r.1.base.scalar.core.queries,
    r.1.ledger.groups,r.1.ledger.completed,(Wgmma.pending r.1.ledger).length,r.1.ledger.calls.length,
    r.1.base.scalar.core.thread.status == .done,lookup "%tile" r.1.base.scalar.core.thread.regs,
    lookup "%out" r.1.base.scalar.core.thread.regs,lookup "%x" r.1.base.scalar.core.thread.regs,
    lookup "%y" r.1.base.scalar.core.thread.regs,lookup "%z" r.1.base.scalar.core.thread.regs,
    lookup "%leader" r.1.base.scalar.core.thread.regs⟩
def initMetadata : Wgmma.Event → Option Nat
  | .base (.barrier e) => match e.operation with | .init _ => some e.location.address | _ => none
  | _ => none
def initialized (tiles : Nat) (lane : Wgmma.Lane) := (source tiles lane).map fun r => r.2.filterMap initMetadata
def transferQueries (tiles : Nat) (lane : Wgmma.Lane) :=
  (source tiles lane).map fun r => r.2.filterMap Ptx.HopperDoubleBufferIterationTests.queryMetadata

theorem six_tile_producer_from_empty : metadata 6 0 = some ⟨85,42,6,6,0,6,false,some 6,some 8192,some 0,some 0,some 0,some 1⟩ := by decide
theorem six_tile_last_lane_from_empty : metadata 6 127 = some ⟨85,18,6,6,0,6,false,some 6,some 8192,some 3,some 7,some 3,some 0⟩ := by decide
theorem six_tile_interior_lane_from_empty : metadata 6 43 = some ⟨85,18,6,6,0,6,false,some 6,some 8192,some 3,some 2,some 1,some 0⟩ := by decide
theorem zero_tile_producer_from_empty : metadata 0 0 = some ⟨85,0,0,0,0,0,false,none,some 8192,some 0,some 0,some 0,some 1⟩ := by decide
theorem zero_tile_peer_from_empty : metadata 0 127 = some ⟨85,0,0,0,0,0,false,none,some 8192,some 3,some 7,some 3,some 0⟩ := by decide
theorem producer_initializes_both_barriers : initialized 6 0 = some [0,8] := by decide
theorem peer_initializes_neither_barrier : initialized 6 127 = some [] := by decide
theorem zero_tile_still_initializes_barriers : initialized 0 0 = some [0,8] := by decide
theorem initial_and_loop_transfer_queries : transferQueries 6 0 = some [0,2,5,7,12,14,19,21,26,28,33,35] := by decide
theorem zero_tile_has_no_transfer : transferQueries 0 0 = some [] := by decide
theorem peer_has_no_transfer : transferQueries 6 127 = some [] := by decide
theorem producer_to_output_fuel : kernelLoopSteps 6 0 = 243 := by decide
theorem peer_to_output_fuel : kernelLoopSteps 6 127 = 189 := by decide

end
end Ptx.HopperDoubleBufferKernelLoopTests
