import Ptx.Kernels.HopperDoubleBufferReplyCandidate
import Ptx.Kernels.HopperDoubleBufferControlGenerations
import Ptx.Hopper.TmaResourceErasure

/-! Compact resource/control metadata for a one-tile source with arbitrary
failed waits and arithmetic/payload replies. The correspondence is proved;
the compact trace is not claimed source-produced or memory-admitted. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def oneTileResourceEvents (lane : Wgmma.Lane) (retries : Nat) : List Hopper.Event :=
  (if HopperStage.leader lane then [
    .barrier ⟨⟨.shared .zero,0⟩,.init 1⟩,.barrier ⟨⟨.shared .zero,8⟩,.init 1⟩,.proxyFenceAsyncShared .zero,
    .ampere (.ordinary (.barrierArrival 0 0)),.ampere (.ordinary (.barrierReturn 0 0)),
    .barrier ⟨⟨.shared .zero,0⟩,.arriveExpectTx 2304⟩,
    .tmaIssue ⟨4096,aView 65536 1,⟨0,0⟩,16,0,0,[]⟩,
    .tmaIssue ⟨4224,bView 131072 1,⟨0,0⟩,2064,0,2,[]⟩]
  else [.ampere (.ordinary (.barrierArrival 0 0)),.ampere (.ordinary (.barrierReturn 0 0))])++
  List.replicate retries (.barrier ⟨⟨.shared .zero,0⟩,.tryWaitParity 0 false⟩)++
  [.barrier ⟨⟨.shared .zero,0⟩,.tryWaitParity 0 true⟩,
   .wgmma .fence,.wgmma .mma,.wgmma .commit,.wgmma .wait,
   .ampere (.ordinary (.barrierArrival 2 0)),.ampere (.ordinary (.barrierReturn 2 0)),
   .wgmma .fence,.wgmma .fence,.wgmma .fence,.wgmma .fence,
   .ampere (.ordinary (.barrierArrival 1 0)),.ampere (.ordinary (.barrierReturn 1 0))]++
  (if HopperStage.leader lane then [.barrier ⟨⟨.shared .zero,0⟩,.inval⟩,.barrier ⟨⟨.shared .zero,8⟩,.inval⟩] else [])

def oneTileResourceTrace (lane : Wgmma.Lane) (retries : Nat) : Hopper.ThreadTrace := {
  id := (ctx 1 lane).id
  oracle := {ampere := {scalar := fun _ => .integer 0,bytes := fun _ => []},wait := fun _ => false}
  count := 0
  final := {}
  events := oneTileResourceEvents lane retries
}

theorem one_tile_resource_events (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat)
    (ha : reply.base.descriptor 0 = aView 65536 1) (hb : reply.base.descriptor 2 = bView 131072 1) :
    ((replyPositiveEvents 1 lane reply retries).map Unified.eventView).map Tma.ResourceErasure.event = oneTileResourceEvents lane (retries 0) := by
  simp only [replyPositiveEvents,replyCheckpoint,loopEvents,loopCheckpoint,Nat.zero_add,
    List.nil_append,iterationEvents,preludeEvents,needsPrefetch,show ¬(0+1 < 1 ∧ HopperStage.leader lane = true) by omega,ite_false,
    List.append_nil,List.map_append,List.map_cons,List.map_nil,List.map_replicate,computeEvents,advanceEvents,
    outputEvents,outputWriteEvents,outputWriteEvent,returnEvents,Unified.eventView,Tma.ResourceErasure.event]
  simp only [Ptx.Event.generation,compute_generations,prepared_generations,iteration_generations,output_generations]
  cases hl : HopperStage.leader lane <;>
    simp [oneTileResourceEvents,initializationEvents,replyInitialCopies,replyInitialA,replyInitialB,ha,hb,waitEvent,hl,
      initialLoopState,generations,Unified.eventView,Tma.ResourceErasure.event,ctx,HopperStage.ctx,barrierAddress,stage,expectedParity]

theorem one_tile_resource_trace (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat)
    (ha : reply.base.descriptor 0 = aView 65536 1) (hb : reply.base.descriptor 2 = bView 131072 1) :
    Tma.ResourceErasure.trace (replyTrace 1 (fun _ => reply) (fun _ => retries) lane).view = oneTileResourceTrace lane (retries 0) := by
  unfold Tma.ResourceErasure.trace oneTileResourceTrace
  congr 1
  exact one_tile_resource_events lane reply retries ha hb

end
end Ptx.Kernels.HopperDoubleBuffer
