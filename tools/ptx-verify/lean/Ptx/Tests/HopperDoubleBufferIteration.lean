import Ptx.Kernels.HopperDoubleBufferIteration
import Ptx.Kernels.HopperDoubleBufferProbeMetadata

/-! Actual source iterations with nonzero accumulator seeds, retained call
history, retries and both producer/consumer paths. Decidable checks project
metadata only; no kernel-memory or arithmetic admission is assumed here. -/
namespace Ptx.HopperDoubleBufferIterationTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def oldCall (group : Nat) : Wgmma.Call := {
  ordinal := group,group := group,lane := 127,d := ⟨"%d0","%d1","%d2","%d3"⟩,
  a := 68720001025,b := 68720001153,scaleD := false,input := fun _ => 0,output := fun _ => 0,query := 0
}
def seed (tile tiles : Nat) (leader : Bool) : Wgmma.State := {
  base := {scalar := {
    core := {thread := {pc := 45,regs := [("%tile",tile),("%tiles",tiles),("%leader",if leader then 1 else 0),
      ("%mapa",4096),("%mapb",4224)]++selectionBindings tile},queries := 7,generations := [(2,tile)]}
    floats := [("%d0",(.f32,17)),("%d1",(.f32,23)),("%d2",(.f32,41)),("%d3",(.f32,59))]
  }}
  ledger := {groups := tile,completed := tile,syncs := 4*tile,calls := (List.range tile).map oldCall}
}
def replies (tiles failed : Nat) : Wgmma.Oracle := {
  base := {
    ampere := {scalar := fun _ => .integer 0,bytes := fun _ => []}
    wait := fun q => decide (7+failed ≤ q)
    descriptor := fun q => if q = 8+failed then aView 65536 tiles else bView 131072 tiles
    tmaBytes := fun q => if q = 9+failed then Ptx.Kernels.HopperStage.aPayload (fun _ => 0) else Ptx.Kernels.HopperStage.bPayload (fun _ => 0)
  }
  matrix := fun q i => ((q+i.val+1 : Nat) : ℝ)
}
def execution (tile tiles failed : Nat) (leader : Bool) :=
  (Wgmma.run (ctx tiles (if leader then 0 else 127)) (replies tiles failed) code
    (iterationSteps tile tiles failed leader) (seed tile tiles leader)).toOption
structure Metadata where
  pc : Nat
  queries : Nat
  groups : Nat
  completed : Nat
  pending : Nat
  callCount : Nat
  tile : Option Nat
  slot : Option Nat
  phase0 : Option Nat
  phase1 : Option Nat
  deriving DecidableEq

def metadata (tile tiles failed : Nat) (leader : Bool) : Option Metadata :=
  (execution tile tiles failed leader).map fun r => ⟨r.1.base.scalar.core.thread.pc,r.1.base.scalar.core.queries,
    r.1.ledger.groups,r.1.ledger.completed,(Wgmma.pending r.1.ledger).length,r.1.ledger.calls.length,
    lookup "%tile" r.1.base.scalar.core.thread.regs,lookup "%slot" r.1.base.scalar.core.thread.regs,
    lookup "%phase0" r.1.base.scalar.core.thread.regs,lookup "%phase1" r.1.base.scalar.core.thread.regs⟩
def transfers (tile tiles failed : Nat) (leader : Bool) :=
  (execution tile tiles failed leader).map fun r => r.2.filterMap transferMetadata
def queryMetadata : Wgmma.Event → Option Nat
  | .base (.tmaIssue copy) => some copy.queryBase
  | _ => none
def transferQueries (tile tiles failed : Nat) (leader : Bool) :=
  (execution tile tiles failed leader).map fun r => r.2.filterMap queryMetadata
def waits (tile tiles failed : Nat) (leader : Bool) :=
  (execution tile tiles failed leader).map fun r => r.2.filterMap waitMetadata
def lastCallMetadata (tile tiles failed : Nat) (leader : Bool) : Option (Nat × Nat × Nat × Nat) :=
  (execution tile tiles failed leader).bind fun r =>
    r.1.ledger.calls.getLast?.map fun call => (call.a,call.b,call.group,call.query)

theorem producer_even_with_retries : metadata 0 3 2 true = some ⟨45,16,1,1,0,1,some 1,some 1,some 1,some 0⟩ := by decide
theorem consumer_even_with_retries : metadata 0 3 2 false = some ⟨45,12,1,1,0,1,some 1,some 1,some 1,some 0⟩ := by decide
theorem producer_odd_with_retry : metadata 1 3 1 true = some ⟨45,15,2,2,0,2,some 2,some 0,some 1,some 1⟩ := by decide
theorem producer_reused_stage : metadata 2 4 0 true = some ⟨45,14,3,3,0,3,some 3,some 1,some 0,some 1⟩ := by decide
theorem producer_final_tile : metadata 3 4 1 true = some ⟨85,11,4,4,0,4,some 4,some 0,some 0,some 0⟩ := by decide
theorem only_tile_enters_output : metadata 0 1 0 true = some ⟨85,10,1,1,0,1,some 1,some 1,some 1,some 0⟩ := by decide
theorem even_prefetch_uses_other_stage : transfers 0 3 2 true = some [(2320,4096,8,8),(4368,4224,1,8)] := by decide
theorem odd_prefetch_uses_other_stage : transfers 1 3 1 true = some [(16,4096,16,0),(2064,4224,2,0)] := by decide
theorem consumer_has_no_prefetch : transfers 0 3 2 false = some [] := by decide
theorem last_producer_has_no_prefetch : transfers 3 4 1 true = some [] := by decide
theorem queries_follow_failed_waits : transferQueries 0 3 2 true = some [10,12] := by decide
theorem retry_events_are_retained : waits 0 3 2 true = some [(0,0,false),(0,0,false),(0,0,true)] := by decide
theorem reused_stage_has_new_parity : waits 2 4 0 true = some [(0,1,true)] := by decide
theorem prefetch_keeps_current_mma_operands : lastCallMetadata 0 3 2 true = some (68720001025,68720001153,0,14) := by decide
theorem odd_prefetch_keeps_current_mma_operands : lastCallMetadata 1 3 1 true = some (68720001169,68720001297,1,13) := by decide

def malformed (tiles failed : Nat) (shortA : Bool) : Wgmma.Oracle :=
  {replies tiles failed with base := {(replies tiles failed).base with
    tmaBytes := fun _ => if shortA then Ptx.Kernels.HopperStage.bPayload (fun _ => 0) else Ptx.Kernels.HopperStage.aPayload (fun _ => 0)}}
def fault (bad : Wgmma.Oracle) (tile tiles failed : Nat) (leader : Bool) : Option Wgmma.Fault :=
  match Wgmma.run (ctx tiles (if leader then 0 else 127)) bad code (iterationSteps tile tiles failed leader) (seed tile tiles leader) with
  | .ok _ => none
  | .error e => some e

theorem short_a_payload_rejected : fault (malformed 3 2 true) 0 3 2 true = some (.base (.tmaPayloadSize 2048 256)) := by decide
theorem oversized_b_payload_rejected : fault (malformed 3 2 false) 0 3 2 true = some (.base (.tmaPayloadSize 256 2048)) := by decide
theorem unused_consumer_payload_unconstrained : fault (malformed 3 2 true) 0 3 2 false = none := by decide
theorem unused_last_tile_payload_unconstrained : fault (malformed 4 1 true) 3 4 1 true = none := by decide

end
end Ptx.HopperDoubleBufferIterationTests
