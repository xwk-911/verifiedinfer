import Ptx.Kernels.ByteValuePipelineMemory

/-! Every admitted RF/co of the actual source supplies the existing native
value checker. Reply equality and read eligibility are conclusions, not input
assumptions. A concrete full memory witness and closed native execution coexist.
-/
namespace Ptx.Kernels.ByteValuePipeline
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic
noncomputable section

theorem writer_precedes_reader (value reply : Nat) (scope : Unified.ClusterScope) (loc : Location) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate value reply) (fun _ => []) scope loc writerMemory readerMemory := by
  apply Unified.base_byte_order
  refine .single (.inl (.inl ⟨?_,?_,rfl,?_⟩))
  · change ((candidate value reply).view.eventAt writer).isSome = true
    rw [writer_view]
    rfl
  · change ((candidate value reply).view.eventAt reader).isSome = true
    rw [reader_view]
    rfl
  · decide

theorem each_actual_read_has_writer {value reply loc byteValue}
    (hr : ByteContents.readByte (candidate value reply) readerMemory loc = some byteValue) :
    ∃ written, ByteContents.writeByte (candidate value reply) writerMemory loc = some written := by
  have hu : ByteAuthority.Uses (candidate value reply) readerControl loc .read := ⟨.kernel,.kernel (ordinary_read_use hr)⟩
  obtain ⟨demand,hd,he,_⟩ := reader_footprint_covers value reply loc .read hu
  obtain ⟨offset,rfl⟩ := List.mem_ofFn.mp hd
  have hw := writer_byte_at value reply offset
  change base.add offset.val = loc at he
  rw [he] at hw
  exact ⟨_,hw⟩

theorem admitted_rf_is_actual_writer {value reply : Nat} {initialProxy : Unified.ProxyMemory} {rf : Unified.ReadsFrom}
    {co : Location → Option Unified.Node → Option Unified.Node → Prop} {scope : Unified.ClusterScope} {loc byteValue}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) scope)
    (hr : ByteContents.readByte (candidate value reply) readerMemory loc = some byteValue) : rf readerMemory loc = some writerMemory := by
  obtain ⟨written,hw⟩ := each_actual_read_has_writer hr
  exact Unified.unique_writer_source hm (every_read_is_eligible value reply scope rf readerMemory loc) hw hr
    (writer_precedes_reader value reply scope loc) (fun _ _ h => writer_only h)

theorem admitted_memory_realizes_native_view {value reply : Nat} {initialProxy : Unified.ProxyMemory} {rf : Unified.ReadsFrom}
    {co : Location → Option Unified.Node → Option Unified.Node → Prop} {scope : Unified.ClusterScope}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) scope) :
    ByteContents.RealizesRF (candidate value reply) initialProxy rf readerMemory (readerGranted value reply) := by
  intro loc byteValue hr
  obtain ⟨written,hw⟩ := each_actual_read_has_writer hr
  exact ByteContentsHeap.producer_to_reader_view (initial := initialProxy) (rf := rf) (context value reply)
    (ByteContentsHeap.acquisitionActions readerControl (demands .read)) (writer_start_has_valid_empty_cut value reply)
    (writer_finishes value reply) hw (reader_claims_run value reply) (reader_is_still_pending_after_claims value reply)
    (only_actual_writer_supplies_phase value reply loc) (admitted_rf_is_actual_writer hm hr)

theorem admitted_memory_passes_value_check {value reply : Nat} {initialProxy : Unified.ProxyMemory} {rf : Unified.ReadsFrom}
    {co : Location → Option Unified.Node → Option Unified.Node → Prop} {scope : Unified.ClusterScope}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) scope) :
    ByteContents.Reads (candidate value reply) readerMemory (readerGranted value reply) :=
  ByteContents.reads_from_agreement hm (fun _ _ _ => every_read_is_eligible value reply scope rf _ _) (admitted_memory_realizes_native_view hm)

theorem admitted_memory_finishes_reader {value reply : Nat} {initialProxy : Unified.ProxyMemory} {rf : Unified.ReadsFrom}
    {co : Location → Option Unified.Node → Option Unified.Node → Prop} {scope : Unified.ClusterScope}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) scope) :
    ByteContents.finish .one (candidate value reply) (fun _ => []) readerMemory (demands .read) (readerGranted value reply) = .ok (afterReader value reply) :=
  ByteContents.finish_succeeds (reader_permissions_finish value reply) (ByteContents.ordinary_linked (reader_view value reply)) (admitted_memory_passes_value_check hm)

theorem admitted_memory_forces_full_word {value reply : Nat} {initialProxy : Unified.ProxyMemory} {rf : Unified.ReadsFrom}
    {co : Location → Option Unified.Node → Option Unified.Node → Prop} {scope : Unified.ClusterScope}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) scope) :
    wrap 32 reply = wrap 32 value := successful_reader_forces_word (admitted_memory_finishes_reader hm)

theorem admitted_memory_source_register {value reply : Nat} {initialProxy : Unified.ProxyMemory} {rf : Unified.ReadsFrom}
    {co : Location → Option Unified.Node → Option Unified.Node → Prop} {scope : Unified.ClusterScope}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) scope) :
    declarationLookup "%r" (trace value reply).final.base.scalar.core.thread.regs = some (wrap 32 value) := by
  rw [loaded_register_is_actual_reply,admitted_memory_forces_full_word hm]

theorem admitted_memory_script_run {value reply : Nat} {initialProxy : Unified.ProxyMemory} {rf : Unified.ReadsFrom}
    {co : Location → Option Unified.Node → Option Unified.Node → Prop} {scope : Unified.ClusterScope}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) scope) :
    IrisExecution.run (ByteContentsHeap.transition (context value reply)) actions initialState = .ok (afterReader value reply) := by
  rw [actions,IrisExecution.run_append,writer_cycle_runs]
  exact ByteContentsHeap.cycle_run (context value reply) _ _ _ _ (writtenValues value reply) (reader_ready_after_writer value reply)
    (reader_footprint_sound value reply) (footprint_distinct _) (reader_pool_comes_from_writer value reply) (admitted_memory_finishes_reader hm)

theorem admitted_memory_native_wp [ByteContentsHeap.GS] {value reply : Nat} {initialProxy : Unified.ProxyMemory} {rf : Unified.ReadsFrom}
    {co : Location → Option Unified.Node → Option Unified.Node → Prop} {scope : Unified.ClusterScope}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) scope)
    (frame : IProp ByteContentsHeap.GF) :
    ByteContentsHeap.control initialState ∗ ByteContentsHeap.freePoints (demands .write) oldValues ∗ frame ⊢
      WP (ByteContentsHeap.script (context value reply) actions)
      {{ result, ⌜result = .ok (afterReader value reply)⌝ ∗ ByteContentsHeap.control (afterReader value reply) ∗
        ByteContentsHeap.freePoints (demands .read) (writtenValues value reply) ∗ frame }} :=
  native_pipeline_wp_of_reader_finish value reply frame (admitted_memory_finishes_reader hm)

theorem admitted_memory_native_adequate {value reply : Nat} {initialProxy : Unified.ProxyMemory} {rf : Unified.ReadsFrom}
    {co : Location → Option Unified.Node → Option Unified.Node → Prop} {scope : Unified.ClusterScope}
    (hm : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate value reply) initialProxy rf co (fun _ => []) scope) :
    adequate .NotStuck (ByteContentsHeap.script (context value reply) actions) initialState (fun result _ => result = .ok (afterReader value reply)) :=
  native_pipeline_closed_adequate_of_reader_finish value reply (admitted_memory_finishes_reader hm)

end
end Ptx.Kernels.ByteValuePipeline
