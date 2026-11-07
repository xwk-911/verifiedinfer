import Ptx.Kernels.HopperDoubleBufferCompute
import Ptx.Kernels.HopperDoubleBufferSourceProbes

/-! Actual source guards, counter bounds and reuse-rendezvous metadata. Only
small decidable projections are evaluated. These do not replace collective or
resource admission and do not grant completion from a CTA barrier. -/
namespace Ptx.HopperDoubleBufferLoopControlTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def seed (pc tile tiles : Nat) (leader : Bool) : Wgmma.State := {
  base := {scalar := {core := {
    thread := {pc := pc,regs := [("%tile",tile),("%tiles",tiles),("%slot",tile%2),("%leader",if leader then 1 else 0)]}
    queries := 13
    generations := [(2,5)]
  }}}
}
def guardResult (tile tiles : Nat) (leader : Bool) :=
  (Wgmma.run (ctx tiles 127) (oracle tiles) code (prefetchGuardSteps tile tiles) (seed 61 tile tiles leader)).toOption
def tailResult (tile tiles : Nat) :=
  (Wgmma.run (ctx tiles 127) (oracle tiles) code 5 (seed 80 tile tiles false)).toOption
def guardMetadata (tile tiles : Nat) (leader : Bool) : Option (Nat × Nat × Option Nat × Option Nat) :=
  (guardResult tile tiles leader).map fun r =>
    (r.1.base.scalar.core.thread.pc,r.1.base.scalar.core.queries,
     lookup "%next" r.1.base.scalar.core.thread.regs,lookup "%more" r.1.base.scalar.core.thread.regs)
def tailMetadata (tile tiles : Nat) : Option (Nat × Nat × Option Nat × Option Nat × Nat × Nat) :=
  (tailResult tile tiles).map fun r =>
    (r.1.base.scalar.core.thread.pc,r.1.base.scalar.core.queries,
     lookup "%tile" r.1.base.scalar.core.thread.regs,lookup "%slot" r.1.base.scalar.core.thread.regs,
     Ptx.Event.generation r.1.base.scalar.core 2,r.2.length)

theorem next_tile_producer_enters_prefetch : guardMetadata 0 3 true = some (65,13,some 1,some 1) := by decide
theorem next_tile_consumer_skips_prefetch : guardMetadata 0 3 false = some (76,13,some 1,some 1) := by decide
theorem last_tile_producer_skips_prefetch : guardMetadata 2 3 true = some (76,13,some 3,some 0) := by decide
theorem last_tile_consumer_skips_prefetch : guardMetadata 2 3 false = some (76,13,some 3,some 0) := by decide
theorem tail_continues_and_toggles_first_stage : tailMetadata 0 3 = some (45,13,some 1,some 1,6,2) := by decide
theorem tail_toggles_second_stage : tailMetadata 1 3 = some (45,13,some 2,some 0,6,2) := by decide
theorem tail_enters_output_at_bound : tailMetadata 2 3 = some (85,13,some 3,some 1,6,2) := by decide
theorem single_tile_enters_output : tailMetadata 0 1 = some (85,13,some 1,some 1,6,2) := by decide
-- Outside the bounded theorem's precondition, actual .u32 addition wraps.
theorem guard_counter_overflow_is_not_nat_successor : guardMetadata 4294967295 4294967295 true =
    some (64,13,some 0,some 1) := by decide

def pendingCall : Wgmma.Call := {
  ordinal := 0,group := 0,lane := 127,d := ⟨"%d0","%d1","%d2","%d3"⟩,
  a := 68720001025,b := 68720001153,scaleD := false,input := fun _ => 0,output := fun _ => 0,query := 0
}
def pendingSeed : Wgmma.State := {seed 80 0 3 false with ledger := {groups := 1,calls := [pendingCall]}}
def rendezvousMetadata : Option (Nat × Nat × Nat) :=
  (Wgmma.run (ctx 3 127) (oracle 3) code 1 pendingSeed).toOption.map fun r =>
    ((Wgmma.pending r.1.ledger).length,r.1.ledger.completed,r.1.base.scalar.core.thread.pc)
theorem rendezvous_preserves_pending_call : rendezvousMetadata = some (1,0,81) := by decide

theorem arbitrary_tail_accumulator_preserved (s : Wgmma.State) (tile tiles : Nat)
    (hn : lookup "%d0" s.base.scalar.core.thread.regs = none) :
    declarationLookup "%d0" (advanceState s tile tiles).base.scalar.floats = declarationLookup "%d0" s.base.scalar.floats :=
  advanceState_float_frame s tile tiles "%d0" (by decide) hn

def computeSeed (tile tiles : Nat) : Wgmma.State := {
  base := {scalar := {
    core := {thread := {pc := 76,regs := [("%ad",68720001025),("%bd",68720001153),
      ("%tile",tile),("%tiles",tiles),("%slot",tile%2)]},queries := 13,generations := [(2,5)]}
    floats := [("%d0",(.f32,17)),("%d1",(.f32,23)),("%d2",(.f32,41)),("%d3",(.f32,59))]
  }}
  ledger := {groups := 3,completed := 3,syncs := 12,calls := [pendingCall,{pendingCall with ordinal := 1,group := 1},{pendingCall with ordinal := 2,group := 2}]}
}
structure NativeMetadata where
  pc : Nat
  queries : Nat
  groups : Nat
  completed : Nat
  callCount : Nat
  pendingCount : Nat
  syncs : Nat
  deriving DecidableEq

def computeMetadata (steps tile tiles : Nat) : Option NativeMetadata :=
  (Wgmma.run (ctx tiles 127) (oracle tiles) code steps (computeSeed tile tiles)).toOption.map fun r =>
    ⟨r.1.base.scalar.core.thread.pc,r.1.base.scalar.core.queries,r.1.ledger.groups,r.1.ledger.completed,
     r.1.ledger.calls.length,(Wgmma.pending r.1.ledger).length,r.1.ledger.syncs⟩
theorem commit_retains_new_pending_call : computeMetadata 3 0 3 = some ⟨79,14,4,3,4,1,15⟩ := by decide
theorem wait_zero_finishes_new_group : computeMetadata 4 0 3 = some ⟨80,15,4,4,4,0,16⟩ := by decide
theorem native_and_tail_continue : computeMetadata 9 0 3 = some ⟨45,15,4,4,4,0,16⟩ := by decide
theorem native_and_tail_enter_output : computeMetadata 9 2 3 = some ⟨85,15,4,4,4,0,16⟩ := by decide

end
end Ptx.HopperDoubleBufferLoopControlTests
