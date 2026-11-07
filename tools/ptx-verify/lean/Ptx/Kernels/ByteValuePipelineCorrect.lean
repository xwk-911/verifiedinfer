import Ptx.Kernels.ByteValuePipelineValues

/-! Every successful two-event value script forces the load's full u32 reply
to equal the stored parameter, modulo the actual PTX u32 representation. Native
local Iris composition and closed heap adequacy use the same checked steps.
-/
namespace Ptx.Kernels.ByteValuePipeline
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def readWitness : Unified.ReadsFrom := fun _ _ => some writerMemory

theorem reader_claims_run (value reply : Nat) :
    IrisExecution.run (ByteContentsHeap.transition (context value reply)) (ByteContentsHeap.acquisitionActions readerControl (demands .read))
      (afterWriter value reply) = .ok (readerGranted value reply) :=
  ByteContentsHeap.acquisition_run (context value reply) (afterWriter value reply) readerControl (demands .read) (writtenValues value reply)
    (reader_ready_after_writer value reply) (reader_footprint_sound value reply) (footprint_distinct _) (reader_pool_comes_from_writer value reply)

theorem writer_start_has_valid_empty_cut (value reply : Nat) :
    Valid .one (candidate value reply) (fun _ => []) (writerGranted value reply).coupled.done := by
  have hc : (writerGranted value reply).coupled = initialState.coupled := ByteContentsHeap.granted_coupled _ _ _ _
  rw [hc]
  exact ⟨fun _ _ _ h => h.elim,fun _ h => h.elim⟩

theorem reader_is_still_pending_after_claims (value reply : Nat) : ¬(readerGranted value reply).coupled.done readerControl := by
  exact (reader_granted_ready value reply).2.1

theorem only_actual_writer_supplies_phase (value reply : Nat) (loc : Location) :
    ByteContentsHeap.PhaseOrder (context value reply) writerMemory readerMemory loc := by
  intro other byteValue hw
  exact Or.inl (writer_only hw)

theorem actual_claim_script_realizes_reader_rf (value : Nat) (initialProxy : Unified.ProxyMemory) :
    ByteContents.RealizesRF (candidate value value) initialProxy readWitness readerMemory (readerGranted value value) := by
  intro loc byteValue hr
  have hw : ByteContents.writeByte (candidate value value) writerMemory loc = some byteValue := (written_and_read_payloads_match value loc).symm.trans hr
  exact ByteContentsHeap.producer_to_reader_view (initial := initialProxy) (rf := readWitness) (context value value)
    (ByteContentsHeap.acquisitionActions readerControl (demands .read)) (writer_start_has_valid_empty_cut value value)
    (writer_finishes value value) hw (reader_claims_run value value) (reader_is_still_pending_after_claims value value)
    (only_actual_writer_supplies_phase value value loc) rfl

theorem reader_granted_payload (value reply : Nat) (offset : Fin 4) :
    get? (readerGranted value reply).cells (ByteAuthority.key (base.add offset.val)) =
      some ⟨.held readerControl .read,some ((payload value)[offset.val]'(by simpa [payload] using offset.isLt))⟩ := by
  have hm : ByteContentsHeap.Matches (readerGranted value reply) readerControl (demands .read) (writtenValues value reply) :=
    ByteContentsHeap.granted_matches _ _ _ _ (footprint_distinct _)
  rw [hm _ (ByteAuthority.Footprint.span_member base 4 .read offset)]
  change some (ByteContents.Payload.mk _ ((ByteContents.writeByte (candidate value reply) writerMemory (base.add offset.val)).or _)) = _
  rw [writer_byte_at]
  rfl

theorem successful_reader_forces_each_byte {value reply next}
    (hs : ByteContents.finish .one (candidate value reply) (fun _ => []) readerMemory (demands .read) (readerGranted value reply) = .ok next)
    (offset : Fin 4) :
    (payload reply)[offset.val]'(by simpa [payload] using offset.isLt) = (payload value)[offset.val]'(by simpa [payload] using offset.isLt) := by
  have hr := (ByteContents.finish_spec hs).2.1 _ _ (reader_byte_at value reply offset)
  unfold ByteContents.valueAt at hr
  rw [reader_granted_payload] at hr
  exact (Option.some.inj hr).symm

theorem successful_reader_forces_word {value reply next}
    (hs : ByteContents.finish .one (candidate value reply) (fun _ => []) readerMemory (demands .read) (readerGranted value reply) = .ok next) :
    wrap 32 reply = wrap 32 value := by
  have hp : payload reply = payload value := by
    apply List.ext_getElem
    · simp [payload]
    · intro i hi hj
      exact successful_reader_forces_each_byte hs ⟨i,by simpa [payload] using hi⟩
  have hd := congrArg (fun bytes : List Symbolic.Byte => decodeLE (bytes.map (fun b => match b with | .bits v => v | _ => byte 0))) hp
  simp only [payload,List.map_map,Function.comp_def] at hd
  change decodeLE ((encodeU32 (wrap 32 reply)).map id) = decodeLE ((encodeU32 (wrap 32 value)).map id) at hd
  simpa only [List.map_id,decode_encodeU32,wrap,Nat.mod_mod] using hd

theorem successful_script_forces_reply {value reply next}
    (hs : IrisExecution.run (ByteContentsHeap.transition (context value reply)) actions initialState = .ok next) :
    wrap 32 reply = wrap 32 value := by
  rw [actions,IrisExecution.run_append,writer_cycle_runs] at hs
  change IrisExecution.run (ByteContentsHeap.transition (context value reply)) (ByteContentsHeap.cycleActions readerMemory (demands .read)) (afterWriter value reply) = .ok next at hs
  have ha := ByteContentsHeap.acquisition_run (context value reply) (afterWriter value reply) readerControl (demands .read) (writtenValues value reply)
    (reader_ready_after_writer value reply) (reader_footprint_sound value reply) (footprint_distinct _) (reader_pool_comes_from_writer value reply)
  rw [ByteContentsHeap.cycleActions,IrisExecution.run_append,show Unified.memoryControlNode readerMemory = readerControl from rfl,ha] at hs
  change IrisExecution.run (ByteContentsHeap.transition (context value reply)) [.finish readerMemory (demands .read)] (readerGranted value reply) = .ok next at hs
  rw [IrisExecution.run_singleton] at hs
  exact successful_reader_forces_word hs

theorem actual_register_correct_of_value_script {value reply next}
    (hs : IrisExecution.run (ByteContentsHeap.transition (context value reply)) actions initialState = .ok next) :
    declarationLookup "%r" (trace value reply).final.base.scalar.core.thread.regs = some (wrap 32 value) := by
  rw [loaded_register_is_actual_reply,successful_script_forces_reply hs]

theorem mismatched_reader_error {value reply}
    (hn : wrap 32 reply ≠ wrap 32 value) :
    ByteContents.finish .one (candidate value reply) (fun _ => []) readerMemory (demands .read) (readerGranted value reply) = .error .readMismatch := by
  apply ByteContents.finish_read_mismatch (reader_permissions_finish value reply) (ByteContents.ordinary_linked (reader_view value reply))
  intro hr
  have hs := ByteContents.finish_succeeds (reader_permissions_finish value reply) (ByteContents.ordinary_linked (reader_view value reply)) hr
  exact hn (successful_reader_forces_word hs)

theorem mismatched_script_error {value reply}
    (hn : wrap 32 reply ≠ wrap 32 value) :
    IrisExecution.run (ByteContentsHeap.transition (context value reply)) actions initialState = .error .readMismatch := by
  rw [actions,IrisExecution.run_append,writer_cycle_runs]
  change IrisExecution.run (ByteContentsHeap.transition (context value reply)) (ByteContentsHeap.cycleActions readerMemory (demands .read)) (afterWriter value reply) = _
  rw [ByteContentsHeap.cycleActions,IrisExecution.run_append,show Unified.memoryControlNode readerMemory = readerControl from rfl,reader_claims_run]
  change IrisExecution.run (ByteContentsHeap.transition (context value reply)) [.finish readerMemory (demands .read)] (readerGranted value reply) = _
  rw [IrisExecution.run_singleton]
  exact mismatched_reader_error hn

theorem final_heap_has_every_written_byte (value : Nat) (offset : Fin 4) :
    ByteContents.valueAt (afterReader value value) (base.add offset.val) =
      some ((payload value)[offset.val]'(by simpa [payload] using offset.isLt)) := by
  rw [ByteContents.finish_preserves_unwritten (reader_finishes value) (by rfl)]
  unfold ByteContents.valueAt
  rw [reader_granted_payload]
  rfl

theorem native_pipeline_wp_of_reader_finish [ByteContentsHeap.GS] (value reply : Nat) (frame : IProp ByteContentsHeap.GF)
    (hs : ByteContents.finish .one (candidate value reply) (fun _ => []) readerMemory (demands .read) (readerGranted value reply) = .ok (afterReader value reply)) :
    ByteContentsHeap.control initialState ∗ ByteContentsHeap.freePoints (demands .write) oldValues ∗ frame ⊢
      WP (ByteContentsHeap.script (context value reply) actions)
      {{ result, ⌜result = .ok (afterReader value reply)⌝ ∗ ByteContentsHeap.control (afterReader value reply) ∗
        ByteContentsHeap.freePoints (demands .read) (writtenValues value reply) ∗ frame }} := by
  apply ByteContentsHeap.cycle_local_cps (context value reply) initialState (afterWriter value reply) writerMemory (demands .write) oldValues
    (ByteContentsHeap.cycleActions readerMemory (demands .read)) frame _ (writer_ready value reply) (writer_footprint_sound value reply)
    (footprint_distinct _) initial_pool_free (writer_finishes value reply)
  exact ByteContentsHeap.cycle_local_wp (context value reply) (afterWriter value reply) (afterReader value reply) readerMemory (demands .read)
    (writtenValues value reply) frame (reader_ready_after_writer value reply) (reader_footprint_sound value reply) (footprint_distinct _)
    (reader_pool_comes_from_writer value reply) hs

theorem native_pipeline_wp [ByteContentsHeap.GS] (value : Nat) (frame : IProp ByteContentsHeap.GF) :
    ByteContentsHeap.control initialState ∗ ByteContentsHeap.freePoints (demands .write) oldValues ∗ frame ⊢
      WP (ByteContentsHeap.script (context value value) actions)
      {{ result, ⌜result = .ok (afterReader value value)⌝ ∗ ByteContentsHeap.control (afterReader value value) ∗
        ByteContentsHeap.freePoints (demands .read) (writtenValues value value) ∗ frame }} :=
  native_pipeline_wp_of_reader_finish value value frame (reader_finishes value)

theorem native_pipeline_closed_adequate_of_reader_finish (value reply : Nat)
    (hs : ByteContents.finish .one (candidate value reply) (fun _ => []) readerMemory (demands .read) (readerGranted value reply) = .ok (afterReader value reply)) :
    adequate .NotStuck (ByteContentsHeap.script (context value reply) actions) initialState (fun result _ => result = .ok (afterReader value reply)) := by
  apply ByteContentsHeap.heap_adequacy
  intro _
  iintro Hall
  icases ByteContentsHeap.allPoints_control_free initialState (demands .write) oldValues (footprint_distinct _) initial_pool_free $$ Hall with ⟨Hcontrol,Hfree⟩
  ihave Hwp := native_pipeline_wp_of_reader_finish value reply iprop(True) hs $$ [$Hcontrol $Hfree]
  iapply wp_mono ?_ $$ Hwp
  intro result
  iintro ⟨%hv,Hcontrol,Hfree,Hframe⟩
  ipureintro; exact hv

theorem native_pipeline_closed_adequate (value : Nat) :
    adequate .NotStuck (ByteContentsHeap.script (context value value) actions) initialState (fun result _ => result = .ok (afterReader value value)) :=
  native_pipeline_closed_adequate_of_reader_finish value value (reader_finishes value)

end
end Ptx.Kernels.ByteValuePipeline
