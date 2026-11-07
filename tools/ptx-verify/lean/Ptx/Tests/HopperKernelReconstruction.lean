import Ptx.Kernels.HopperDoubleBufferKernelReconstruction
import Ptx.Kernels.HopperDoubleBufferDataSource
import Ptx.Tests.HopperLoopReconstruction

/-! Full source paths: producer retries, all zero-tile lanes with hostile
unused replies, short initial copies and consumer elision. Source replay is
separate from matrix correctness and full resource/memory/runtime admission.
-/
namespace Ptx.HopperKernelReconstructionTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev retryReply := HopperIterationReconstructionTests.retryOracle
abbrev producerResult := HopperIterationReconstructionTests.producerResult
def fullCount : Nat := initialSteps true+HopperIterationReconstructionTests.producerCount
def fullEvents : List Wgmma.Event := initializationEvents true++replyInitialCopies retryReply true++producerResult.2

theorem full_producer_source : Wgmma.run (ctx 2 0) retryReply code fullCount {} = .ok (producerResult.1,fullEvents) := by
  have hshape : HopperStage.leader (0 : Wgmma.Lane) = true →
      (retryReply.base.tmaBytes 1).length = (retryReply.base.descriptor 0).bytes ∧
      (retryReply.base.tmaBytes 3).length = (retryReply.base.descriptor 2).bytes := by intro _; decide
  have hinit := positive_initial_any_reply 2 0 retryReply (by decide) (by decide) hshape
  rw [show HopperStage.leader (0 : Wgmma.Lane) = true from by decide] at hinit
  have hrun : Wgmma.run (ctx 2 0) retryReply code HopperIterationReconstructionTests.producerCount (initialLoopState 2 0 true) = .ok producerResult :=
    HopperIterationReconstructionTests.producer_source_produced
  rw [fullCount,Wgmma.run_add,hinit]
  simp only [Except.bind]
  rw [hrun]
  simp only [fullEvents,List.append_assoc]

theorem full_producer_reconstructed :
    ∃ retries, retries 0 = 3 ∧ retries 1 = 0 ∧ fullCount = replyPositiveSteps 2 0 retries ∧
      producerResult.1 = replyPositiveState 2 0 retryReply retries ∧ fullEvents = replyPositiveEvents 2 0 retryReply retries := by
  obtain ⟨retries,_,hr,hcount,hstate,hevents⟩ := completed_positive_source_reconstruct (by decide) (by decide)
    full_producer_source HopperIterationReconstructionTests.producer_source_done
  have he := HopperLoopReconstructionTests.producer_schedule_unique hr
  exact ⟨retries,he.1,he.2,hcount,hstate,hevents⟩

def hostileReply : Wgmma.Oracle := {oracle 0 with
  base := {(oracle 0).base with tmaBytes := fun _ => [],wait := fun _ => false}
  matrix := fun _ _ => 999
  completed := fun _ => 999
  operands := fun _ _ => .bits (byte 255)}

theorem all_zero_tile_lanes_ignore_unused_replies (lane : Wgmma.Lane) :
    Wgmma.run (ctx 0 lane) hostileReply code (completeSteps 0 lane) {} = .ok (completeState 0 lane,completeEvents 0 lane) :=
  zero_complete_any_reply lane hostileReply

theorem arbitrary_zero_completion_count {lane count last events}
    (hn : Wgmma.run (ctx 0 lane) hostileReply code count {} = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    count = completeSteps 0 lane ∧ last = completeState 0 lane ∧ events = completeEvents 0 lane := completed_zero_source_reconstruct hn hd

def shortAReply : Wgmma.Oracle := {oracle 2 with base := {(oracle 2).base with
  tmaBytes := fun q => if q = 1 then [] else (oracle 2).base.tmaBytes q}}
def shortBReply : Wgmma.Oracle := {oracle 2 with base := {(oracle 2).base with
  tmaBytes := fun q => if q = 3 then [] else (oracle 2).base.tmaBytes q}}

theorem short_initial_a_cannot_complete :
    ¬∃ count last events, Wgmma.run (ctx 2 0) shortAReply code count {} = .ok (last,events) ∧ last.base.scalar.core.thread.status = .done := by
  rintro ⟨count,last,events,hn,hd⟩
  have hs := completed_kernel_initial_shapes (by decide) (by decide) hn hd rfl
  have hb : (shortAReply.base.tmaBytes 1).length ≠ (shortAReply.base.descriptor 0).bytes := by decide
  exact hb hs.1

theorem short_initial_b_cannot_complete :
    ¬∃ count last events, Wgmma.run (ctx 2 0) shortBReply code count {} = .ok (last,events) ∧ last.base.scalar.core.thread.status = .done := by
  rintro ⟨count,last,events,hn,hd⟩
  have hs := completed_kernel_initial_shapes (by decide) (by decide) hn hd rfl
  have hb : (shortBReply.base.tmaBytes 3).length ≠ (shortBReply.base.descriptor 2).bytes := by decide
  exact hb hs.2

theorem short_b_keeps_initial_a : shortBReply.base.tmaBytes 1 = (oracle 2).base.tmaBytes 1 := by
  simp only [shortBReply,show ¬(1 = 3) from by decide,ite_false]

def emptyUnusedReply : Wgmma.Oracle := {oracle 2 with base := {(oracle 2).base with tmaBytes := fun _ => []}}
theorem full_consumer_skips_unused_initial_and_prefetch_replies :
    ((Wgmma.run (ctx 2 127) emptyUnusedReply code (completeSteps 2 127) {}).toOption.map
      (fun result => result.1.base.scalar.core.thread.status == .done)) = some true := by decide

theorem arbitrary_real_candidate_trace_has_source_shape (a : TileA) (b : TileB) (tiles : Nat) (hb : tiles ≤ 2^28)
    (initial : Location → Symbolic.Byte) (trace : Unified.ThreadTrace) (ht : trace ∈ (dataCompleteCandidate a b tiles).traces) :
    ∃ lane : Wgmma.Lane, trace.id = (ctx tiles lane).id ∧
      ((tiles = 0 ∧ trace.count = completeSteps 0 lane ∧ trace.final = completeState 0 lane ∧ trace.events = completeEvents 0 lane) ∨
       (0 < tiles ∧ ∃ retries, trace.count = replyPositiveSteps tiles lane retries ∧
         trace.final = replyPositiveState tiles lane trace.oracle retries ∧ trace.events = replyPositiveEvents tiles lane trace.oracle retries)) :=
  completed_candidate_trace_reconstruct hb (data_source_well_formed a b tiles initial hb) (data_candidate_local a b tiles hb) ht

theorem zero_completed_source_cannot_be_padded (lane : Wgmma.Lane) :
    Wgmma.run (ctx 0 lane) hostileReply code (completeSteps 0 lane+1) {} = .error .blocked := by
  rw [Wgmma.run_add,zero_complete_any_reply]
  simp only [Except.bind,Wgmma.run_done_suffix (complete_source_status 0 lane (by decide)).1 0]

end
end Ptx.HopperKernelReconstructionTests
