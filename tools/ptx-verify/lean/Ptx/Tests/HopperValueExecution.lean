import Ptx.Kernels.HopperDoubleBufferValueOutput
import Ptx.Tests.HopperRetryDataMemory

/-! Complete actual Hopper value-prefix witnesses, final matrix fragments and
source-readiness counterexamples. Native adequacy initializes the actual map;
no physical sm_90a execution, IEEE storage or host drain/acquire is asserted.
-/
namespace Ptx.HopperValueExecutionTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

abbrev schedule := HopperRetryDataTests.schedule
abbrev frame := HopperRetryDataTests.frame
abbrev family := HopperRetryDataTests.family
abbrev candidate := HopperRetryDataTests.candidate
def protocol := Whole.prepared (List.replicate 10 0) 3
def initialState (a b) := retryValueInitialState a b 3 schedule frame protocol
def ctx (a b) := byteContentsContext (family a b)
def prefilled (a b) (tile : Fin 3) (operand : Wgmma.OperandByte) :=
  ByteContents.withValue (initialState a b) (retryNativeLocation (family a b) tile operand) (some (((family a b).calls tile 0).operandBytes operand.index))

theorem actual_initial_future_read_invariant (a b) :
    ByteContentsHeap.FutureReads (ctx a b) (dataInitialProxyMemory a b 3 frame) (retryDataReadWitness a b 3 schedule) (initialState a b) :=
  retry_value_initial_future a b 3 schedule frame protocol (by decide) (by decide)

theorem both_arenas_and_reuse_have_proved_frontiers (a b) : ByteContentsHeap.ReadFrontier (ctx a b) (retryDataReadWitness a b 3 schedule) :=
  retry_value_read_frontier a b 3 schedule (by decide) (by decide)

theorem all_actual_reads_have_derived_eligibility (a b read loc value)
    (hr : ByteContents.readByte (candidate a b) read loc = some value) :
    Unified.Eligible Tma.localShared Access.globalDescriptor (candidate a b) (retryHistories (family a b)) dataCluster (retryDataReadWitness a b 3 schedule) read loc :=
  retry_value_read_eligible a b 3 schedule (by decide) (by decide) read loc value hr

theorem actual_complete_value_source_prefix (a b) :
    ∃ actions next, IrisExecution.run (ByteContentsHeap.transition (ctx a b)) actions (initialState a b) = .ok next ∧
      next.coupled.done = Present (candidate a b) ∧ next.coupled.protocol = protocol ∧ ByteContentsHeap.Available next ∧
      ByteContentsHeap.Allocated next (Whole.byteLocations (family a b)) :=
  retry_data_value_source_run a b 3 schedule frame protocol (by decide) (by decide)

theorem actual_full_prefix_has_closed_native_adequacy (a b) :
    ∃ actions next, IrisExecution.run (ByteContentsHeap.transition (ctx a b)) actions (initialState a b) = .ok next ∧
      next.coupled.done = Present (candidate a b) ∧ next.coupled.protocol = protocol ∧ ByteContentsHeap.Available next ∧
      adequate .NotStuck (ByteContentsHeap.script (ctx a b) actions) (initialState a b) (fun result _ => result = .ok next) :=
  retry_data_value_native_witness a b 3 schedule frame protocol (by decide) (by decide)

theorem completed_script_retains_prepared_protocol (a b actions next)
    (hr : IrisExecution.run (ByteContentsHeap.transition (ctx a b)) actions (initialState a b) = .ok next) : next.coupled.protocol = protocol :=
  ByteContentsHeap.run_protocol _ actions hr

theorem actual_values_project_to_prior_authority (a b) :
    ∃ actions next, IrisExecution.run (ByteContentsHeap.transition (ctx a b)) actions (initialState a b) = .ok next ∧
      next.coupled = ⟨protocol,Present (candidate a b)⟩ ∧
      ByteAuthority.Steps HopperStage.block (candidate a b) (retryHistories (family a b)) dataCluster (Whole.plan (family a b))
        (ByteContents.erase (initialState a b)) (ByteContents.erase next) :=
  retry_data_prepared_value_source a b 3 schedule frame (List.replicate 10 0) (by decide) (by decide)

theorem native_heap_final_matrix_is_correct (a b actions next)
    (hr : IrisExecution.run (ByteContentsHeap.transition (ctx a b)) actions (initialState a b) = .ok next)
    (hc : next.coupled.done = Present (candidate a b)) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt next ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      some (.realPart .f32 (specification a b 3 (Wgmma.cCoord (lane,slot))) index.val) :=
  retry_data_value_output_of_run (by decide) (by decide) hr hc lane slot index

theorem nonzero_three_tile_native_matrix_witness :
    ∃ actions next, IrisExecution.run (ByteContentsHeap.transition (ctx (fun _ _ => 1) (fun _ _ => 2))) actions
      (initialState (fun _ _ => 1) (fun _ _ => 2)) = .ok next ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4),
        ByteContents.valueAt next ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 96 index.val)) ∧
      adequate .NotStuck (ByteContentsHeap.script (ctx (fun _ _ => 1) (fun _ _ => 2)) actions)
        (initialState (fun _ _ => 1) (fun _ _ => 2)) (fun result _ => result = .ok next) := by
  obtain ⟨actions,next,hr,hcut,hp,ha,hm,hadequate⟩ := retry_data_value_matrix_witness (fun _ _ => 1) (fun _ _ => 2) 3 schedule frame protocol (by decide) (by decide)
  refine ⟨actions,next,hr,?_,hadequate⟩
  intro lane slot index
  have hs := HopperRetryDataTests.nonzero_three_tile_accumulation lane slot
  rw [retry_data_final_accumulation] at hs
  rw [hm lane slot index,hs]

theorem actual_operand_is_allocated (a b) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    (get? (initialState a b).cells (ByteAuthority.key (retryNativeLocation (family a b) tile operand))).isSome = true := by
  have hw := HopperRetryDataMemoryTests.source a b
  have hc := retry_data_complete a b 3 schedule (by decide) (by decide)
  have hd := (HopperRetryDataMemoryTests.positive_joint_components a b).1.descriptors
  have hr := retry_native_read_byte (family a b) hw tile tile.isLt operand
  have hu := ByteContents.actual_read_use (candidate_no_nonbulk (by decide) hw hc) hr
  have hl := Whole.byte_inventory_bounded (family a b) (by decide) (by decide) hw hc hd _ _ _ hu
  exact ByteContentsHeap.initial_cells_allocated _ _ _ _ hl

theorem prefilled_operand_has_the_actual_desired_value (a b) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    ByteContents.valueAt (prefilled a b tile operand) (retryNativeLocation (family a b) tile operand) = some (((family a b).calls tile 0).operandBytes operand.index) := by
  obtain ⟨payload,hg⟩ := Option.isSome_iff_exists.mp (actual_operand_is_allocated a b tile operand)
  exact ByteContents.withValue_lookup hg

theorem correct_data_does_not_bypass_tma_source_readiness (a b) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    ByteContents.claim HopperStage.block (candidate a b) (retryHistories (family a b))
      ⟨Unified.memoryControlNode (retryNativeRead (family a b) tile operand),retryNativeLocation (family a b) tile operand,.read⟩
      (prefilled a b tile operand) = .error (.authority .unready) := by
  apply ByteContents.claim_unready
  intro hr
  have hp : (prefilled a b tile operand).coupled = (initialState a b).coupled :=
    ByteContents.withValue_coupled (initialState a b) (retryNativeLocation (family a b) tile operand) (some (((family a b).calls tile 0).operandBytes operand.index))
  rw [hp] at hr
  have hv : Valid HopperStage.block (candidate a b) (retryHistories (family a b)) (initialState a b).coupled.done :=
    ⟨fun _ _ _ h => h.elim,fun _ h => h.elim⟩
  exact retry_value_native_ready_needs_producer a b 3 schedule (by decide) (by decide) tile tile.isLt operand _ hv hr

end
end Ptx.HopperValueExecutionTests
