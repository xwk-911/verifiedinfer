import Ptx.Kernels.HopperDoubleBufferValueFrontier
import Ptx.Kernels.HopperDoubleBufferProgress

/-! Nonvacuous complete source-prefix value execution for every bounded
positive-K data/retry family. Actual descriptors, TMA data, native operands,
ordinary stores, resources and arrivals pass their original checks. Closed
adequacy uses the existing whole-map native script helper; the new cycle
construction itself still performs each real claim and completion separately.
Host/device drain/acquire and physical allocation/runtime refinement are separate.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris.ProgramLogic
noncomputable section

theorem retry_data_value_source_run (a b tiles schedules frame protocol) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∃ actions next,
      IrisExecution.run (ByteContentsHeap.transition (byteContentsContext (retryDataFamily a b tiles schedules))) actions
        (retryValueInitialState a b tiles schedules frame protocol) = .ok next ∧
      next.coupled.done = Present (retryDataCandidate a b tiles schedules) ∧
      next.coupled.protocol = protocol ∧ ByteContentsHeap.Available next ∧
      ByteContentsHeap.Allocated next (Whole.byteLocations (retryDataFamily a b tiles schedules)) := by
  let family := retryDataFamily a b tiles schedules
  have hw := retry_data_source a b tiles schedules (dataRepresentedInitial a b tiles frame) ht hb
  have hc := retry_data_complete a b tiles schedules ht hb
  have hd := retry_data_descriptors a b tiles schedules ht hb
  have hm := retry_data_memory_witness a b tiles schedules frame ht hb
  obtain ⟨actions,next,hrun,hcut,ha,hl,_⟩ := ByteContentsHeap.reached_value_witness (byteContentsContext family) (Whole.byteLocations family)
    (retryValueInitialState a b tiles schedules frame protocol) hm.toCausalConstraints
    (retry_value_read_eligible a b tiles schedules ht hb) (candidate_no_nonbulk hb hw hc)
    (Whole.byte_inventory_bounded family ht hb hw hc hd) (retry_value_read_frontier a b tiles schedules ht hb)
    (retry_value_initial_future a b tiles schedules frame protocol ht hb)
    (ByteContentsHeap.initial_cells_available _ _ _) (ByteContentsHeap.initial_cells_allocated _ _ _) rfl
    (retry_data_full_prefix a b tiles schedules ht hb)
  exact ⟨actions,next,hrun,hcut,ByteContentsHeap.run_protocol _ actions hrun,ha,hl⟩

theorem retry_data_value_native_witness (a b tiles schedules frame protocol) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∃ actions next,
      IrisExecution.run (ByteContentsHeap.transition (byteContentsContext (retryDataFamily a b tiles schedules))) actions
        (retryValueInitialState a b tiles schedules frame protocol) = .ok next ∧
      next.coupled.done = Present (retryDataCandidate a b tiles schedules) ∧
      next.coupled.protocol = protocol ∧ ByteContentsHeap.Available next ∧
      adequate .NotStuck (ByteContentsHeap.script (byteContentsContext (retryDataFamily a b tiles schedules)) actions)
        (retryValueInitialState a b tiles schedules frame protocol) (fun result _ => result = .ok next) := by
  obtain ⟨actions,next,hrun,hcut,hprotocol,ha,_⟩ := retry_data_value_source_run a b tiles schedules frame protocol ht hb
  exact ⟨actions,next,hrun,hcut,hprotocol,ha,ByteContentsHeap.script_adequate _ _ _ _ hrun⟩

theorem retry_data_prepared_value_source (a b tiles schedules frame values) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∃ actions next,
      IrisExecution.run (ByteContentsHeap.transition (byteContentsContext (retryDataFamily a b tiles schedules))) actions
        (retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles)) = .ok next ∧
      next.coupled = ⟨Whole.prepared values tiles,Present (retryDataCandidate a b tiles schedules)⟩ ∧
      ByteAuthority.Steps HopperStage.block (retryDataCandidate a b tiles schedules) (retryHistories (retryDataFamily a b tiles schedules))
        dataCluster (Whole.plan (retryDataFamily a b tiles schedules))
        (ByteContents.erase (retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles))) (ByteContents.erase next) := by
  obtain ⟨actions,next,hrun,hcut,hprotocol,_,_⟩ := retry_data_value_source_run a b tiles schedules frame (Whole.prepared values tiles) ht hb
  refine ⟨actions,next,hrun,?_,ByteContentsHeap.run_projects _ actions hrun⟩
  exact congrArg₂ Bridge.State.mk hprotocol hcut

end
end Ptx.Kernels.HopperDoubleBuffer
