import Ptx.Kernels.HopperDoubleBufferFullValues
import Ptx.Tests.HopperKernelOwnership

/-! Zero-K is not an empty source: all output stores and opaque barrier
reservations execute. Nonzero initial bytes are overwritten by real zero
fragments; resource cell payloads remain opaque. No GPU test is asserted.
-/
namespace Ptx.HopperZeroValueTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
open Iris Iris.BI Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def initial : Location → Symbolic.Byte := fun _ => .bits (byte 99)
def values : List Nat := [13,29]
def raw := zeroValueInitialState zeroCandidate initial (Ptx.Async.initial 1 values)
def prepared := zeroValueInitialState zeroCandidate initial (zeroValuePrepared values)
def ctx := zeroValuePreparationContext zeroCandidate

theorem actual_zero_source_with_nonzero_initial_bytes : Unified.WellFormed code (completeLaunch 0 initial) zeroCandidate :=
  data_source_well_formed (fun _ _ => 0) (fun _ _ => 0) 0 initial (by decide)
theorem actual_zero_source_is_complete : Unified.Complete zeroCandidate := data_candidate_local _ _ 0 (by decide)

theorem minimal_two_region_queue_has_no_input_or_descriptor_reservation :
    KernelLease.commands kernelReservations = [.access 0 .write,.access 1 .write] := rfl

theorem initial_protocol_has_no_loans : raw.coupled.protocol.buffers.map (fun b => b.loans.length) = [0,0] := rfl

theorem arbitrary_zero_source_has_no_reads {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) (read : Unified.Node) (loc : Location) :
    ByteContents.readByte candidate read loc = none := completed_zero_no_reads hw hc read loc

theorem actual_source_still_writes_every_matrix_fragment (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.writeByte zeroCandidate (.base (.tma (.source (zeroStoreId lane slot))))
      ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 0 index.val) :=
  completed_zero_output_byte actual_zero_source_with_nonzero_initial_bytes actual_zero_source_is_complete lane slot index

theorem output_cells_start_with_nonzero_bits (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt raw ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.bits (byte 99)) := by
  have hwrite := actual_source_still_writes_every_matrix_fragment lane slot index
  have hu := ByteContents.actual_write_use (candidate_no_nonbulk (by decide) actual_zero_source_with_nonzero_initial_bytes actual_zero_source_is_complete) hwrite
  have hl := zero_value_inventory_bounded actual_zero_source_with_nonzero_initial_bytes actual_zero_source_is_complete _ _ _ hu
  have hg := ByteContents.initialCells_member (initial := initial) hl
  change (get? (ByteContents.initialCells zeroValueLocations initial) _).bind ByteContents.Payload.value = _
  rw [hg]
  rfl

theorem actual_initialization_and_invalidation_cover_both_barrier_spans (slot : Stage) (offset : Fin 8) :
    ByteAuthority.Uses zeroCandidate (.base (.source (dataInitId 0 slot))) ((dataGate slot).add offset.val) .write ∧
      ByteAuthority.Uses zeroCandidate (.base (.source (dataInvalId (fun _ _ => 0) (fun _ _ => 0) 0 slot))) ((dataGate slot).add offset.val) .write :=
  ⟨⟨.kernel,.kernel (HopperKernelOwnershipTests.zero_initialization_uses_all_storage_bytes slot offset)⟩,
    ⟨.kernel,.kernel (HopperKernelOwnershipTests.zero_invalidation_uses_all_storage_bytes slot offset)⟩⟩

theorem every_actual_use_is_in_the_two_region_pool {node loc mode} (hu : ByteAuthority.Uses zeroCandidate node loc mode) :
    loc ∈ zeroValueLocations := zero_value_inventory_bounded actual_zero_source_with_nonzero_initial_bytes actual_zero_source_is_complete node loc mode hu

theorem native_public_preparation_starts_without_loans :
    IrisExecution.run (ByteContentsPreparation.transition ctx) zeroValuePreparationActions raw = .ok prepared :=
  (zero_value_native_preparation zeroCandidate initial values rfl).1

theorem native_zero_client_has_matrix_and_returned_loans :
    ∃ actions final,
      IrisExecution.run (ByteContentsPreparation.transition ctx) (zeroValuePublicActions actions) raw = .ok final ∧
      final.coupled = ⟨zeroValueReturned values,Present zeroCandidate⟩ ∧ ByteContentsHeap.Available final ∧
      Ptx.Async.Drain.Returned final.coupled.protocol ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4), ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 0 index.val)) ∧
      adequate .NotStuck (ByteContentsPreparation.script ctx (zeroValuePublicActions actions)) raw (fun result _ => result = .ok final) := by
  obtain ⟨actions,final,hr,hc,ha,hrtn,hlive,hm,hreuse,hadequate⟩ := zero_value_public_witness values rfl actual_zero_source_with_nonzero_initial_bytes actual_zero_source_is_complete
  exact ⟨actions,final,hr,hc,ha,hrtn,hm,hadequate⟩

theorem every_completed_zero_source_has_a_full_native_client {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    ∃ actions final,
      IrisExecution.run (ByteContentsPreparation.transition (zeroValuePreparationContext candidate)) (zeroValuePublicActions actions)
        (zeroValueInitialState candidate initial (Ptx.Async.initial 1 values)) = .ok final ∧
      Ptx.Async.Drain.Returned final.coupled.protocol ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4), ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 0 index.val)) := by
  obtain ⟨actions,final,hr,_,_,hrtn,_,hm,_,_⟩ := zero_value_public_witness values rfl hw hc
  exact ⟨actions,final,hr,hrtn,hm⟩

theorem arbitrary_successful_complete_client_has_zero_matrix (actions final)
    (hr : IrisExecution.run (ByteContentsPreparation.transition ctx) actions raw = .ok final)
    (hc : final.coupled.done = Present zeroCandidate) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 0 index.val) :=
  zero_value_public_output_of_run actual_zero_source_with_nonzero_initial_bytes actual_zero_source_is_complete hr hc lane slot index

theorem barrier_storage_payloads_are_preserved_in_the_opaque_model (actions final)
    (hr : IrisExecution.run (ByteContentsPreparation.transition ctx) actions raw = .ok final) (slot : Stage) (offset : Fin 8) :
    ByteContents.valueAt final ((dataGate slot).add offset.val) = some (.bits (byte 99)) := by
  rw [zero_value_public_frame_of_run actual_zero_source_with_nonzero_initial_bytes actual_zero_source_is_complete hr (by
    simp [Regions.Region.Contains,outputStorageRegion,dataGate,barrierAddress,Location.add])]
  have hl : (dataGate slot).add offset.val ∈ zeroValueLocations := by
    unfold zeroValueLocations
    exact List.mem_append.mpr (.inr (ByteAuthority.Footprint.mem_regionLocations (barrier_storage_contains slot offset.isLt)))
  have hg := ByteContents.initialCells_member (initial := initial) hl
  change (get? (ByteContents.initialCells zeroValueLocations initial) _).bind ByteContents.Payload.value = _
  rw [hg]
  rfl

def outputOnlyProtocol := (Ptx.Async.step (Ptx.Async.initial 1 values) (.access 0 0 .write)).toOption.getD (Ptx.Async.initial 1 values)
def outputOnly := zeroValueInitialState zeroCandidate initial outputOnlyProtocol
theorem omitting_the_barrier_reservation_cannot_seal : ByteContentsPreparation.transition ctx .seal outputOnly = .error .preparationNotReady := by
  apply ByteContentsPreparation.seal_incomplete
  · exact ⟨⟨fun _ h => h,ByteContentsHeap.initial_cells_available _ _ _⟩,by decide⟩
  · intro hr
    have hn : outputOnlyProtocol.streams ≠ [⟨2,0,[.access 0 .write,.access 1 .write],[]⟩] := by decide
    exact hn hr.1

def preparedStream : Ptx.Async.Stream := ⟨2,0,[.access 0 .write,.access 1 .write],[]⟩
def firstDevice := (Ptx.Async.deviceStep (zeroValuePrepared values) 0).toOption.getD (zeroValuePrepared values)
theorem scalar_fifo_is_ready_before_zero_source_executes : Ptx.Async.deviceStep (zeroValuePrepared values) 0 = .ok firstDevice := by decide
theorem next_kernel_work_is_not_complete_despite_zero_k :
    ¬ByteAuthority.NextCompleted zeroCandidate zeroHistories dataCluster (KernelLease.plan 2) (fun _ => False) 0 preparedStream := by
  intro hp
  have hh := hp .kernel (by simp [KernelLease.plan,preparedStream])
  cases hh with
  | kernel _ hdone => exact hdone _ HopperKernelOwnershipTests.actual_zero_init_is_present

theorem zero_k_device_cannot_skip_actual_source_work :
    ByteContentsPreparation.transition ctx (.execute (.protocol (.device 0))) prepared = .error (.authority .incompleteWork) := by
  change ByteContentsPreparation.transition (zeroValuePreparationContext zeroCandidate) (.execute (.protocol (.device 0)))
    (zeroValueInitialState zeroCandidate initial (zeroValuePrepared values)) = _
  rw [ByteContentsPreparation.execution_step (zero_value_native_preparation zeroCandidate initial values rfl).2]
  apply ByteContentsProtocolHeap.protocol_error
  exact ByteAuthority.execute_device_uncompleted (st := preparedStream) (by decide) scalar_fifo_is_ready_before_zero_source_executes next_kernel_work_is_not_complete_despite_zero_k

theorem missing_second_completion_cannot_acquire :
    Ptx.Async.run (zeroValuePrepared values) [.device 0,.acquire 0] = .error .notComplete := by decide
theorem before_acquire_the_barrier_region_still_has_a_loan :
    Ptx.Async.run (zeroValuePrepared values) [.device 0,.device 0,.reclaim 1] = .error .outstandingLoan := by decide

theorem returned_both_regions_can_be_reused_or_reclaimed (bid : Fin 2) :
    (∃ next, Ptx.Async.reclaim (zeroValueReturned values) bid.val = .ok next) ∧
      ∀ value, ∃ next, Ptx.Async.hostWrite (zeroValueReturned values) bid.val value = .ok next := by
  have hp := zero_value_return_succeeds values rfl
  have hb : bid.val < (zeroValueReturned values).buffers.length := by rw [hp.2.2.2]; exact bid.isLt
  exact ⟨Ptx.Async.Drain.returned_can_reclaim hp.2.1 hp.2.2.1 bid hb,fun value => Ptx.Async.Drain.returned_can_write hp.2.1 hp.2.2.1 bid value hb⟩

theorem one_native_contract_covers_every_bounded_k (a b tiles schedules) (hb : tiles ≤ 2^28) :
    ∃ actions final,
      IrisExecution.run (ByteContentsPreparation.transition (fullValueContext a b tiles schedules)) (fullValueActions tiles actions)
        (fullValueInitialState a b tiles schedules initial (List.replicate (fullValueBufferCount tiles) 0)) = .ok final ∧
      Ptx.Async.Drain.Returned final.coupled.protocol ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4), ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
        some (.realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val)) ∧
      adequate .NotStuck (ByteContentsPreparation.script (fullValueContext a b tiles schedules) (fullValueActions tiles actions))
        (fullValueInitialState a b tiles schedules initial (List.replicate (fullValueBufferCount tiles) 0)) (fun result _ => result = .ok final) := by
  obtain ⟨actions,final,hr,hc,ha,hrtn,hlive,hm,hreuse,hadequate⟩ := full_value_native_witness a b tiles schedules initial
    (List.replicate (fullValueBufferCount tiles) 0) (by simp) hb
  exact ⟨actions,final,hr,hrtn,hm,hadequate⟩

theorem any_successful_unified_client_has_the_same_matrix (a b tiles schedules protocolValues actions final) (hb : tiles ≤ 2^28)
    (hr : IrisExecution.run (ByteContentsPreparation.transition (fullValueContext a b tiles schedules)) actions
      (fullValueInitialState a b tiles schedules initial protocolValues) = .ok final)
    (hc : final.coupled.done = Present (fullValueCandidate a b tiles schedules)) (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      some (.realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val) :=
  full_value_output_of_run hb hr hc lane slot index

end
end Ptx.HopperZeroValueTests
