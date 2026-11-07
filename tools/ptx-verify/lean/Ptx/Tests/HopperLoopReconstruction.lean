import Ptx.Kernels.HopperDoubleBufferLoopReconstruction
import Ptx.Tests.HopperIterationReconstruction
import Ptx.Tests.HopperSourceReconstruction

/-! Whole-loop reconstruction on actual producer/consumer source suffixes.
Future retry entries preserve full prefixes but are not globally unique;
incorrect entries in executed tiles are rejected. No real equality decider.
-/
namespace Ptx.HopperLoopReconstructionTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev producerStart := HopperIterationReconstructionTests.producerStart
abbrev producerOracle := HopperIterationReconstructionTests.retryOracle
abbrev producerCount := HopperIterationReconstructionTests.producerCount
abbrev producerResult := HopperIterationReconstructionTests.producerResult
def plan (tile : Nat) : Nat := if tile = 0 then 3 else 0
def futurePlan : Nat → Nat := Function.update plan 2 99

theorem producer_plan_replies : ∀ i < 2,
    LoopReplies producerOracle (loopQuery 0 2 true plan producerStart.base.scalar.core.queries i) i 2 (plan i) true := by
  intro i hi
  have he : i = 0 ∨ i = 1 := by omega
  rcases he with rfl | rfl
  · simpa only [loopQuery,plan,ite_true] using HopperIterationReconstructionTests.actual_replies_extracted
  · refine ⟨by intro j hj; change j < 0 at hj; omega,by decide,?_⟩
    intro hn
    exact (by have hh := hn.1; omega)

theorem producer_schedule_unique {retries : Nat → Nat}
    (hr : ∀ i < 2, LoopReplies producerOracle (loopQuery 0 2 true retries producerStart.base.scalar.core.queries i) i 2 (retries i) true) :
    retries 0 = 3 ∧ retries 1 = 0 := by
  have he := loop_reply_schedules_unique (first := 0) (tiles := 2) (leader := true)
    (query := producerStart.base.scalar.core.queries) (n := 2)
    (by simpa only [Nat.zero_add] using hr) (by simpa only [Nat.zero_add] using producer_plan_replies)
  exact ⟨he 0 (by decide),he 1 (by decide)⟩

theorem producer_whole_loop_reconstructed :
    loopFuel 0 2 true plan 2 < producerCount ∧
    (loopCheckpoint (ctx 2 0) producerOracle 0 2 true plan producerStart (fun _ => 0) 2).1.base.scalar.core.thread.pc = 85 ∧
    Wgmma.pending (loopCheckpoint (ctx 2 0) producerOracle 0 2 true plan producerStart (fun _ => 0) 2).1.ledger = [] ∧
    ∃ tailEvents, Wgmma.run (ctx 2 0) producerOracle code (producerCount-loopFuel 0 2 true plan 2)
      (loopCheckpoint (ctx 2 0) producerOracle 0 2 true plan producerStart (fun _ => 0) 2).1 = .ok (producerResult.1,tailEvents) ∧
      producerResult.2 = loopEvents (ctx 2 0) producerOracle 0 2 true plan producerStart (fun _ => 0) 4096 4224 2++tailEvents := by
  exact completed_loop_reconstruct_at_schedule (ctx := ctx 2 0)
    (by rfl) (by rfl) (by rfl) (by decide) (initial_loop_registers 2 0 true (by decide)) (initial_loop_accumulators 2 0 true)
    (by decide) (by decide) HopperIterationReconstructionTests.producer_source_produced HopperIterationReconstructionTests.producer_source_done
    (by simpa only [Nat.zero_add] using producer_plan_replies)

theorem actual_query_schedule : loopQuery 0 2 true plan 4 1 = 14 ∧ loopQuery 0 2 true plan 4 2 = 17 := by decide
theorem losing_executed_retries_changes_queries : loopQuery 0 2 true plan 4 1 ≠ loopQuery 0 2 true (fun _ => 0) 4 1 := by decide

theorem future_retry_update_preserves_prefix (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (values : Fin 4 → ℝ) :
    loopQuery 0 2 true futurePlan s.base.scalar.core.queries 2 = loopQuery 0 2 true plan s.base.scalar.core.queries 2 ∧
    loopFuel 0 2 true futurePlan 2 = loopFuel 0 2 true plan 2 ∧
    loopCheckpoint ctx oracle 0 2 true futurePlan s values 2 = loopCheckpoint ctx oracle 0 2 true plan s values 2 ∧
    loopEvents ctx oracle 0 2 true futurePlan s values 4096 4224 2 = loopEvents ctx oracle 0 2 true plan s values 4096 4224 2 := by
  have he : ∀ i < 2, futurePlan (0+i) = plan (0+i) := by
    intro i hi
    exact Function.update_of_ne (by omega) _ _
  exact ⟨loop_query_retry_congr he,loop_fuel_retry_congr he,loop_checkpoint_retry_congr he,loop_events_retry_congr he⟩

theorem future_schedule_also_compatible : ∀ i < 2,
    LoopReplies producerOracle (loopQuery 0 2 true futurePlan producerStart.base.scalar.core.queries i) i 2 (futurePlan i) true := by
  intro i hi
  have he : ∀ j < 2, futurePlan (0+j) = plan (0+j) := by intro j hj; exact Function.update_of_ne (by omega) _ _
  rw [loop_query_retry_congr (tiles := 2) (leader := true) (fun j hj => he j (by omega : j < 2)),
    show futurePlan i = plan i from by simpa only [Nat.zero_add] using he i hi]
  exact producer_plan_replies i hi

theorem future_entries_are_not_globally_unique : futurePlan ≠ plan := by
  intro he
  have hh := congrFun he 2
  change 99 = 0 at hh
  omega

theorem wrong_executed_schedule_rejected {retries : Nat → Nat} (hb : retries 0 ≠ 3 ∨ retries 1 ≠ 0) :
    ¬(∀ i < 2, LoopReplies producerOracle (loopQuery 0 2 true retries producerStart.base.scalar.core.queries i) i 2 (retries i) true) := by
  intro hr
  have he := producer_schedule_unique hr
  rcases hb with hb | hb
  · exact hb he.1
  · exact hb he.2

theorem consumer_whole_loop_reconstructed :
    ∃ retries, retries 0 = 3 ∧
      (loopCheckpoint (ctx 1 127) HopperSourceReconstructionTests.retryOracle 0 1 false retries
        HopperSourceReconstructionTests.headerStart (fun _ => 0) 1).1.base.scalar.core.thread.pc = 85 ∧
      ∃ tailEvents, Wgmma.run (ctx 1 127) HopperSourceReconstructionTests.retryOracle code
        (HopperSourceReconstructionTests.headerCount-loopFuel 0 1 false retries 1)
        (loopCheckpoint (ctx 1 127) HopperSourceReconstructionTests.retryOracle 0 1 false retries
          HopperSourceReconstructionTests.headerStart (fun _ => 0) 1).1 = .ok (HopperSourceReconstructionTests.waitResult.1,tailEvents) ∧
        HopperSourceReconstructionTests.waitResult.2 = loopEvents (ctx 1 127) HopperSourceReconstructionTests.retryOracle 0 1 false retries
          HopperSourceReconstructionTests.headerStart (fun _ => 0) 4096 4224 1++tailEvents := by
  obtain ⟨retries,hr,_,hpc,_,htail⟩ := completed_loop_reconstruct (ctx := ctx 1 127)
    (by rfl) (by rfl) (by rfl) (by decide) (initial_loop_registers 1 127 false (by decide)) (initial_loop_accumulators 1 127 false)
    (by decide) (by decide) HopperSourceReconstructionTests.actual_header_produced HopperSourceReconstructionTests.wait_source_done
  have hs := hr 0 (by decide)
  have he := first_wait_success_unique hs.1 hs.2.1 HopperSourceReconstructionTests.actual_first_success_conditions.1
    HopperSourceReconstructionTests.actual_first_success_conditions.2
  exact ⟨retries,he,hpc,htail⟩

end
end Ptx.HopperLoopReconstructionTests
