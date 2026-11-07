import Ptx.Kernels.ByteValuePipelineCorrect

/-! Actual generated source, nonvacuous native two-event execution, complete
word correctness and wrong-data/partial-permission rejection. These are model
checks; no GPU or physical allocation/compiler refinement is asserted.
-/
namespace Ptx.ByteValuePipelineTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels.ByteValuePipeline
open Iris Iris.BI Iris.ProgramLogic
noncomputable section

theorem mechanically_translated_five_instructions : Generated.byte_value_pipeline.program.length = 5 := by rfl

theorem actual_source_is_complete_even_for_wrong_reply :
    Unified.Produced program (params 7) .one (trace 7 0) ∧ Unified.Complete (candidate 7 0) :=
  ⟨source_produced 7 0,source_complete 7 0⟩

theorem actual_launch_coverage_with_wrong_reply : Unified.WellFormed program (launch 7) (candidate 7 0) := source_well_formed 7 0

theorem both_events_and_all_claims_are_physical_steps : actions.length = 10 := by rfl

theorem full_word_source_has_actual_value_execution :
    IrisExecution.run (ByteContentsHeap.transition (context 305419896 305419896)) actions initialState = .ok (afterReader 305419896 305419896) :=
  actual_two_event_value_script 305419896

theorem source_register_contains_full_word : declarationLookup "%r" (trace 305419896 305419896).final.base.scalar.core.thread.regs = some 305419896 := by rfl

theorem source_register_obeys_u32_wrapping : declarationLookup "%r" (trace 4294967303 4294967303).final.base.scalar.core.thread.regs = some 7 := by rfl

theorem any_successful_reply_is_forced (value reply : Nat) (next : ByteContents.State)
    (hs : IrisExecution.run (ByteContentsHeap.transition (context value reply)) actions initialState = .ok next) :
    declarationLookup "%r" (trace value reply).final.base.scalar.core.thread.regs = some (wrap 32 value) :=
  actual_register_correct_of_value_script hs

theorem final_bytes_are_little_endian :
    List.ofFn (fun i : Fin 4 => ByteContents.valueAt (afterReader 305419896 305419896) (base.add i.val)) =
      [some (.bits (byte 120)),some (.bits (byte 86)),some (.bits (byte 52)),some (.bits (byte 18))] := by
  simp only [final_heap_has_every_written_byte]
  rfl

theorem upper_word_bytes_are_checked :
    ByteContents.finish .one (candidate 305419896 22136) (fun _ => []) readerMemory (demands .read) (readerGranted 305419896 22136) = .error .readMismatch :=
  mismatched_reader_error (by decide)

theorem wrong_reply_passes_all_permission_checks :
    ByteAuthority.Footprint.finish .one (candidate 7 0) (fun _ => []) readerControl (demands .read) (ByteContents.erase (readerGranted 7 0)) =
      .ok (ByteAuthority.retired (ByteContents.erase (readerGranted 7 0)) readerControl) :=
  reader_permissions_finish 7 0

theorem wrong_reply_fails_actual_value_check :
    ByteContents.finish .one (candidate 7 0) (fun _ => []) readerMemory (demands .read) (readerGranted 7 0) = .error .readMismatch :=
  mismatched_reader_error (by decide)

theorem wrong_reply_fails_after_actual_writer_and_all_claims :
    IrisExecution.run (ByteContentsHeap.transition (context 7 0)) actions initialState = .error .readMismatch :=
  mismatched_script_error (by decide)

theorem incomplete_reader_footprint_cannot_succeed (value : Nat) :
    ∀ next, ByteContents.finish .one (candidate value value) (fun _ => []) readerMemory (ByteAuthority.Footprint.span base 3 .read) (readerGranted value value) ≠ .ok next := by
  intro next hs
  have hf := ByteAuthority.Footprint.finish_spec (ByteContents.authority_finish_of_value_finish hs)
  have hu := reader_footprint_sound value value ⟨base.add 3,.read⟩ (ByteAuthority.Footprint.span_member base 4 .read (3 : Fin 4))
  obtain ⟨demand,hd,he,_⟩ := hf.2.2.1 (base.add 3) .read hu
  obtain ⟨offset,rfl⟩ := List.mem_ofFn.mp hd
  have ha := congrArg Location.address he
  change 64+offset.val = 64+3 at ha
  have hb := offset.isLt
  omega

theorem actual_pipeline_native_heap_initialization (value : Nat) :
    adequate .NotStuck (ByteContentsHeap.script (context value value) actions) initialState (fun result _ => result = .ok (afterReader value value)) :=
  native_pipeline_closed_adequate value

theorem real_claim_script_supplies_rf_view (value : Nat) (initialProxy : Unified.ProxyMemory) :
    ByteContents.RealizesRF (candidate value value) initialProxy readWitness readerMemory (readerGranted value value) :=
  actual_claim_script_realizes_reader_rf value initialProxy

end
end Ptx.ByteValuePipelineTests
