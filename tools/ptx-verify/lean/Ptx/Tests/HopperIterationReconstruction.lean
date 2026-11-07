import Ptx.Kernels.HopperDoubleBufferIterationReconstruction
import Ptx.Kernels.HopperDoubleBufferKernelSource
import Ptx.Kernels.HopperDoubleBufferProbeMetadata

/-! Actual producer execution with failed waits and prefetch, inverse reply
extraction and malformed A/B payload rejection. No memory/resource admission
or hardware equality follows from these finite source tests. -/
namespace Ptx.HopperIterationReconstructionTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def producerStart : Wgmma.State := initialLoopState 2 0 true
def retryOracle : Wgmma.Oracle := {oracle 2 with base := {(oracle 2).base with
  wait := fun q => decide (7 ≤ q)
  descriptor := fun q => if q = 8 then aView 65536 2 else (oracle 2).base.descriptor q
  tmaBytes := fun q => if q = 9 then HopperStage.aPayload (fun _ => 0) else (oracle 2).base.tmaBytes q}}
def producerCount : Nat := completeSteps 2 0-initialSteps true+6
def producerRun := Wgmma.run (ctx 2 0) retryOracle code producerCount producerStart
def producerResult : Wgmma.State × List Wgmma.Event := producerRun.toOption.getD ({},[])

theorem producer_source_succeeds : producerRun.toOption.isSome = true := by decide
theorem producer_complete_metadata : ((producerResult.1.base.scalar.core.thread.status == .done) &&
    decide (producerResult.1.ledger.groups = 2) && decide (producerResult.1.ledger.completed = 2)) = true := by decide
theorem producer_source_produced : producerRun = .ok producerResult := by
  cases hs : producerRun with
  | error fault => have hh := producer_source_succeeds; rw [hs] at hh; cases hh
  | ok value => simp only [producerResult,hs,Except.toOption,Option.getD_some]
theorem producer_source_done : producerResult.1.base.scalar.core.thread.status = .done := by
  have h := producer_complete_metadata
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  tauto
theorem producer_failed_waits_retained : (producerResult.2.filterMap waitMetadata).take 4 =
    [(0,0,false),(0,0,false),(0,0,false),(0,0,true)] := by decide
def issuedSizes : Wgmma.Event → Option (Nat × Nat × Nat)
  | .base (.tmaIssue op) => some (op.queryBase,op.descriptor.bytes,op.payload.length)
  | _ => none
theorem actual_prefetch_keeps_full_a_b_extents : producerResult.2.filterMap issuedSizes =
    [(8,2048,2048),(10,256,256)] := by decide

theorem producer_first_success_conditions :
    (∀ i < 3, retryOracle.base.wait (producerStart.base.scalar.core.queries+i) = false) ∧
      retryOracle.base.wait (producerStart.base.scalar.core.queries+3) = true := by
  refine ⟨?_,by decide⟩
  intro i hi
  change decide (7 ≤ 4+i) = false
  simp only [decide_eq_false_iff_not]
  omega

theorem actual_replies_extracted : LoopReplies retryOracle producerStart.base.scalar.core.queries 0 2 3 true := by
  have hregs := initial_loop_registers 2 0 true (by decide)
  obtain ⟨r,hs⟩ := completed_iteration_replies (ctx := ctx 2 0) (by rfl) (by rfl) (by rfl) hregs
    (by decide) (by decide) producer_source_produced producer_source_done
  have he := first_wait_success_unique hs.1 hs.2.1 producer_first_success_conditions.1 producer_first_success_conditions.2
  subst r
  exact hs

theorem actual_prefetch_lengths_derived :
    (retryOracle.base.tmaBytes 9).length = (retryOracle.base.descriptor 8).bytes ∧
      (retryOracle.base.tmaBytes 11).length = (retryOracle.base.descriptor 10).bytes :=
  actual_replies_extracted.2.2 (by decide)

theorem actual_iteration_reconstructed :
    ∃ tailEvents, Wgmma.run (ctx 2 0) retryOracle code (producerCount-iterationSteps 0 2 3 true)
      (iterationState (ctx 2 0) retryOracle producerStart 0 2 3 true (fun _ => 0)) = .ok (producerResult.1,tailEvents) ∧
      producerResult.2 = iterationEvents (ctx 2 0) retryOracle producerStart 0 2 3 true 4096 4224 (fun _ => 0)++tailEvents := by
  obtain ⟨r,hs,_,ht⟩ := completed_iteration_reconstruct (ctx := ctx 2 0) (by rfl) (by rfl) (by rfl) (by decide)
    (initial_loop_registers 2 0 true (by decide)) (initial_loop_accumulators 2 0 true)
    (by decide) (by decide) producer_source_produced producer_source_done
  have he := first_wait_success_unique hs.1 hs.2.1 producer_first_success_conditions.1 producer_first_success_conditions.2
  subst r
  exact ht

def transferStart : Wgmma.State := prefetchAddressState (prefetchGuardState (headerState producerStart 0 3) 0 2 true) 0 1
def shortAOracle : Wgmma.Oracle := {retryOracle with base := {retryOracle.base with tmaBytes := fun _ => []}}
def shortBOracle : Wgmma.Oracle := {retryOracle with base := {retryOracle.base with
  tmaBytes := fun query => if query = 11 then [] else retryOracle.base.tmaBytes query}}

theorem short_a_payload_cannot_complete :
    ¬∃ count last events, Wgmma.run (ctx 2 0) shortAOracle code count transferStart = .ok (last,events) ∧
      last.base.scalar.core.thread.status = .done := by
  rintro ⟨count,last,events,hn,hd⟩
  have hs := completed_transfer_shapes (ctx := ctx 2 0) (oracle := shortAOracle) (s := transferStart) (slot := 1)
    (next := 1) (mapA := 4096) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hn hd
  have hbad : (shortAOracle.base.tmaBytes (transferStart.base.scalar.core.queries+1)).length ≠
      (shortAOracle.base.descriptor transferStart.base.scalar.core.queries).bytes := by decide
  exact hbad hs.1

theorem short_b_payload_cannot_complete :
    ¬∃ count last events, Wgmma.run (ctx 2 0) shortBOracle code count transferStart = .ok (last,events) ∧
      last.base.scalar.core.thread.status = .done := by
  rintro ⟨count,last,events,hn,hd⟩
  have hs := completed_transfer_shapes (ctx := ctx 2 0) (oracle := shortBOracle) (s := transferStart) (slot := 1)
    (next := 1) (mapA := 4096) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hn hd
  have hbad : (shortBOracle.base.tmaBytes (transferStart.base.scalar.core.queries+3)).length ≠
      (shortBOracle.base.descriptor (transferStart.base.scalar.core.queries+2)).bytes := by decide
  exact hbad hs.2

theorem short_b_keeps_a_reply : shortBOracle.base.tmaBytes 9 = retryOracle.base.tmaBytes 9 := by
  simp only [shortBOracle,show ¬(9 = 11) from by decide,ite_false]

def skippedResult (leader : Bool) : Option (Wgmma.State × List Wgmma.Event) :=
  let lane : Wgmma.Lane := if leader then 0 else 127
  (Wgmma.run (ctx 1 lane) ({oracle 1 with base := {(oracle 1).base with tmaBytes := fun _ => []}} : Wgmma.Oracle) code
    (completeSteps 1 lane-initialSteps leader) (initialLoopState 1 lane leader)).toOption
theorem unused_short_payload_last_tile_accepted :
    ((skippedResult true).map (fun r => r.1.base.scalar.core.thread.status == .done)) = some true := by decide
theorem unused_short_payload_consumer_accepted :
    ((skippedResult false).map (fun r => r.1.base.scalar.core.thread.status == .done)) = some true := by decide

end
end Ptx.HopperIterationReconstructionTests
