import Ptx.Kernels.HopperDoubleBufferByteContents
import Ptx.Tests.ByteContentsFootprint
import Ptx.Tests.HopperRetryDataMemory

/-! Checked RMW transitions and real-data Hopper writer partitions. The Hopper
tests establish applicability of the phase premise on both arenas and reuse;
they do not exhibit a full native value script reaching an operand read.
-/
namespace Ptx.ByteContentsPhasesTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
open Ptx.ByteRetirementTests Ptx.ByteAcquisitionTests Ptx.ByteContentsTests
noncomputable section

theorem initial_source_cut_is_valid : Valid .one rmwCandidate (fun _ => []) initialState.coupled.done := by
  exact ⟨fun _ _ _ h => h.elim,fun _ h => h.elim⟩

theorem actual_script_preserves_source_validity : Valid .one rmwCandidate (fun _ => []) finalState.coupled.done :=
  ByteContentsHeap.run_valid ctx actions initial_source_cut_is_valid actual_value_script_run

theorem checked_claim_preserves_every_value (index : Fin 4) (loc : Location) :
    ByteContents.valueAt (acquiredState (index.val+1)) loc = ByteContents.valueAt (acquiredState index.val) loc :=
  ByteContents.claim_preserves_value (actual_claim_succeeds index) loc

theorem actual_write_determines_returned_counter : ByteContents.valueAt finalState AtomicMemoryTests.base = some (.bits (byte 1)) :=
  ByteContents.finish_writes_byte finish_checks_permissions_and_values (by rfl)

theorem actual_nonwriter_preserves_other_location :
    ByteContents.valueAt finalState ByteContentsFootprintTests.spare = ByteContents.valueAt (acquiredState 4) ByteContentsFootprintTests.spare :=
  ByteContents.finish_preserves_unwritten finish_checks_permissions_and_values (by rfl)

theorem actual_write_preserves_allocated_spare :
    ByteContents.valueAt ByteContentsFootprintTests.framedFinal ByteContentsFootprintTests.spare =
      ByteContents.valueAt ByteContentsFootprintTests.framedAcquired ByteContentsFootprintTests.spare :=
  ByteContents.finish_preserves_unwritten ByteContentsFootprintTests.adding_spare_preserves_all_source_and_value_checks (by rfl)

theorem actual_finish_records_source_completion : finalState.coupled.done rmwNode := Or.inr rfl

theorem finished_source_cannot_be_fresh_again : ¬ByteAuthority.Ready .one rmwCandidate (fun _ => []) finalState.coupled.done rmwNode := by
  intro h
  exact h.2.1 actual_finish_records_source_completion

theorem real_data_has_all_byte_phase_partitions (a b) (tile : Fin 3) (operand : Wgmma.OperandByte) :
    ByteContentsHeap.PhaseOrder (byteContentsContext (HopperRetryDataTests.family a b))
      (retryNativeProducer (HopperRetryDataTests.family a b) tile operand)
      (retryNativeRead (HopperRetryDataTests.family a b) tile operand)
      (retryNativeLocation (HopperRetryDataTests.family a b) tile operand) :=
  retry_byte_contents_phase (HopperRetryDataTests.family a b) (HopperRetryDataMemoryTests.source a b)
    (retry_data_complete a b 3 HopperRetryDataTests.schedule (by decide) (by decide))
    (HopperRetryDataMemoryTests.positive_joint_components a b).1.descriptors (by decide) tile tile.isLt operand

theorem reused_location_has_current_phase_partition (a b) (operand : Wgmma.OperandByte) :
    ByteContentsHeap.PhaseOrder (byteContentsContext (HopperRetryDataTests.family a b))
      (retryNativeProducer (HopperRetryDataTests.family a b) 2 operand)
      (retryNativeRead (HopperRetryDataTests.family a b) 2 operand)
      (retryNativeLocation (HopperRetryDataTests.family a b) 0 operand) := by
  rw [retry_native_location_same_stage (HopperRetryDataTests.family a b) 0 2 (by decide) operand]
  exact real_data_has_all_byte_phase_partitions a b (2 : Fin 3) operand

end
end Ptx.ByteContentsPhasesTests
