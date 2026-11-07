import Ptx.Kernels.HopperDoubleBufferKernelReconstruction
import Ptx.Kernels.HopperDoubleBufferSourceFootprints

/-! Exhaustive ordinary-access and output inventories for arbitrary completed
source replies, then arbitrary well-formed completed candidates. Output values
are captured source accumulators, not an assumed matrix specification. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem reply_initial_memory_shape (reply : Wgmma.Oracle) (leader : Bool) :
    (replyInitialCopies reply leader).all sourceMemoryShape = true := by cases leader <;> rfl

theorem wait_replicate_memory_shape (context : Scalar.Context) (bar parity retries : Nat) (answer : Bool) :
    (List.replicate retries (waitEvent context bar parity answer)).all sourceMemoryShape = true := by
  induction retries with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.all_cons]; exact ih

theorem reply_iteration_memory_shape (context oracle s tile tiles retries leader mapA mapB values) :
    (iterationEvents context oracle s tile tiles retries leader mapA mapB values).all sourceMemoryShape = true := by
  simp only [iterationEvents,List.all_append,wait_replicate_memory_shape,prelude_memory_shape]
  rfl

theorem reply_loop_memory_shape (context oracle first tiles leader retries s values mapA mapB n) :
    (loopEvents context oracle first tiles leader retries s values mapA mapB n).all sourceMemoryShape = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [loopEvents,List.all_append,ih,reply_iteration_memory_shape]; rfl

theorem reply_positive_memory_shape (tiles lane reply retries) :
    (replyPositiveEvents tiles lane reply retries).all sourceMemoryShape = true := by
  simp only [replyPositiveEvents,List.all_append,initialization_memory_shape,reply_initial_memory_shape,reply_loop_memory_shape,output_memory_shape]
  rfl

theorem zero_complete_memory_shape (lane : Wgmma.Lane) : (completeEvents 0 lane).all sourceMemoryShape = true := by
  simp only [completeEvents,preOutputEvents,preOutputState,ite_true,List.all_append,initialization_memory_shape,output_memory_shape]
  rfl

theorem reply_initial_no_global_write (reply : Wgmma.Oracle) (leader : Bool) :
    (replyInitialCopies reply leader).filterMap globalWrite = [] := by cases leader <;> rfl

theorem reply_positive_write_inventory (tiles lane reply retries) :
    (replyPositiveEvents tiles lane reply retries).filterMap globalWrite = List.ofFn (fun slot : Wgmma.Slot =>
      (outputWordAddress (lane,slot),Symbolic.encode .f32 ((replyCheckpoint tiles lane reply retries).2 slot))) := by
  simp only [replyPositiveEvents,outputEvents,List.filterMap_append,initialization_no_global_write,
    reply_initial_no_global_write,loop_no_global_write,return_no_global_write,List.nil_append,List.append_nil,output_write_inventory]
  congr 1
  funext slot
  rw [output_write_address]
  rfl

theorem candidate_trace_memory_shape {tiles initial candidate trace} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (ht : trace ∈ candidate.traces) : trace.events.all sourceMemoryShape = true := by
  obtain ⟨lane,_,hzero | hpositive⟩ := completed_candidate_trace_reconstruct hb hw hc ht
  · rw [hzero.2.2.2]; exact zero_complete_memory_shape lane
  · obtain ⟨_,retries,_,_,he⟩ := hpositive
    rw [he]; exact reply_positive_memory_shape tiles lane trace.oracle retries

theorem candidate_trace_write_inventory {tiles initial candidate trace} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (ht : trace ∈ candidate.traces) :
    ∃ lane : Wgmma.Lane, trace.id = (ctx tiles lane).id ∧ ∃ values : Wgmma.Slot → ℝ,
      trace.events.filterMap globalWrite = List.ofFn (fun slot : Wgmma.Slot =>
        (outputWordAddress (lane,slot),Symbolic.encode .f32 (values slot))) := by
  obtain ⟨lane,hid,hzero | hpositive⟩ := completed_candidate_trace_reconstruct hb hw hc ht
  · refine ⟨lane,hid,fun _ => 0,?_⟩
    rw [hzero.2.2.2,complete_write_inventory]
    rfl
  · obtain ⟨_,retries,_,_,he⟩ := hpositive
    refine ⟨lane,hid,(replyCheckpoint tiles lane trace.oracle retries).2,?_⟩
    rw [he]; exact reply_positive_write_inventory tiles lane trace.oracle retries

theorem candidate_event_memory_shape {tiles initial candidate id event} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (he : candidate.eventAt id = some event) : sourceMemoryShape event = true := by
  obtain ⟨trace,ht,_,hget⟩ := Unified.eventAt_trace he
  exact List.all_eq_true.mp (candidate_trace_memory_shape hb hw hc ht) event (List.mem_of_getElem? hget)

theorem candidate_view_memory_shape {tiles initial candidate id event} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (he : candidate.view.eventAt id = some event) : memoryShape event = true := by
  rw [Unified.view_eventAt] at he
  obtain ⟨rich,hr,rfl⟩ := Option.map_eq_some_iff.mp he
  exact candidate_event_memory_shape hb hw hc hr

end
end Ptx.Kernels.HopperDoubleBuffer
