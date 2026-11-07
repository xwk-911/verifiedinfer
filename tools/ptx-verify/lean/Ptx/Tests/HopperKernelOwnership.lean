import Ptx.Kernels.HopperDoubleBufferKernelOwnership

/-! Actual zero/positive source uses, complete conservative source-coupled
lifetimes, omitted barrier coverage and early return counterexamples.
No GPU execution or physical byte/allocation simulation is claimed. -/
namespace Ptx.HopperKernelOwnershipTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section

abbrev values : List Nat := [0,0]
def prepared : Ptx.Async.State := {
  streams := [⟨2,0,[.access 0 .write,.access 1 .write],[]⟩]
  buffers := [{loans := [⟨⟨0,1⟩,.write⟩]},{loans := [⟨⟨0,2⟩,.write⟩]}]
  events := [⟨0,⟨0,2⟩⟩]
}
theorem public_preparation_exact :
    Ptx.Async.run (Ptx.Async.initial 1 values) (KernelLease.prepareActions kernelReservations) = .ok prepared := by rfl

theorem zero_source_checked : Unified.WellFormed code (completeLaunch 0 (fun _ => .bits 0)) zeroCandidate :=
  data_source_well_formed (fun _ _ => 0) (fun _ _ => 0) 0 _ (by decide)
theorem zero_source_complete : Unified.Complete zeroCandidate := data_candidate_local _ _ 0 (by decide)

theorem zero_initialization_uses_all_storage_bytes (slot : Stage) (offset : Fin 8) :
    KernelUse Tma.localShared zeroCandidate (.base (.source (dataInitId 0 slot))) ((dataGate slot).add offset.val) .write :=
  .resource (data_resource_init _ _ 0 slot) offset.isLt

theorem zero_invalidation_uses_all_storage_bytes (slot : Stage) (offset : Fin 8) :
    KernelUse Tma.localShared zeroCandidate (.base (.source (dataInvalId (fun _ _ => 0) (fun _ _ => 0) 0 slot)))
      ((dataGate slot).add offset.val) .write := .resource (data_resource_inval _ _ 0 slot) offset.isLt

theorem zero_stores_have_actual_byte_uses (lane : Wgmma.Lane) (slot : Wgmma.Slot) (offset : Fin 4) :
    KernelUse Tma.localShared zeroCandidate (.base (.source (zeroStoreId lane slot)))
      ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add offset.val) .write :=
  ordinary_write_use (completed_zero_output_byte zero_source_checked zero_source_complete lane slot offset)

theorem zero_ordinary_resource_coverage : KernelLease.Covers Tma.localShared zeroCandidate kernelReservations :=
  zero_kernel_use_coverage zero_source_checked zero_source_complete

theorem actual_zero_init_is_present : Present zeroCandidate (.base (.source (dataInitId 0 0))) :=
  kernel_use_present (zero_initialization_uses_all_storage_bytes 0 0)

theorem local_termination_does_not_complete_empty_prefix :
    ¬Completed Tma.localShared zeroCandidate zeroHistories dataCluster (fun _ => False) .kernel :=
  pending_kernel_use_not_completed (zero_initialization_uses_all_storage_bytes 0 0) (by simp)

theorem full_actual_prefix_completes_kernel :
    Completed Tma.localShared zeroCandidate zeroHistories dataCluster (Present zeroCandidate) .kernel :=
  .kernel zero_source_complete (fun _ h => h)

theorem public_preparation_derives_all_reservations : Regions.Borrowed (KernelLease.bindings kernelReservations) prepared := by
  obtain ⟨hr,hi,_⟩ := KernelLease.preparation_properties (kernel_reservations_valid values rfl) public_preparation_exact
  exact KernelLease.prepared_bindings_borrowed hr hi

theorem pending_source_init_protects_barrier {state : Bridge.State}
    (hs : Bridge.Steps HopperStage.block Tma.localShared zeroCandidate zeroHistories dataCluster (KernelLease.plan 2)
      ⟨prepared,fun _ => False⟩ state)
    (hp : ¬state.done (.base (.source (dataInitId 0 0)))) :
    Ptx.Async.reclaim state.protocol 1 = .error .outstandingLoan ∧
      ∀ value, Ptx.Async.hostWrite state.protocol 1 value = .error .outstandingLoan :=
  zero_kernel_public_pending_rejected rfl public_preparation_exact zero_source_checked zero_source_complete hs
    (zero_initialization_uses_all_storage_bytes 0 0) hp rfl (barrier_storage_contains 0 (by decide))

theorem pending_source_store_protects_output {state : Bridge.State} (lane : Wgmma.Lane) (slot : Wgmma.Slot)
    (hs : Bridge.Steps HopperStage.block Tma.localShared zeroCandidate zeroHistories dataCluster (KernelLease.plan 2)
      ⟨prepared,fun _ => False⟩ state)
    (hp : ¬state.done (.base (.source (zeroStoreId lane slot)))) : Ptx.Async.reclaim state.protocol 0 = .error .outstandingLoan := by
  have hu := zero_stores_have_actual_byte_uses lane slot 0
  have hr := ordinary_write_in_output (by decide) zero_source_checked zero_source_complete
    (completed_zero_output_byte zero_source_checked zero_source_complete lane slot 0)
  exact (zero_kernel_public_pending_rejected rfl public_preparation_exact zero_source_checked zero_source_complete hs hu hp rfl hr).1

theorem zero_source_has_public_coupled_lifetime :
    ∃ final, Bridge.Steps HopperStage.block Tma.localShared zeroCandidate zeroHistories dataCluster (KernelLease.plan 2)
      ⟨prepared,fun _ => False⟩ ⟨final,Present zeroCandidate⟩ ∧ Ptx.Async.Drain.Returned final := by
  obtain ⟨actual,final,ha,_,hs,_,hr,_⟩ := zero_kernel_public_coupled_return values rfl zero_source_checked zero_source_complete (cluster := dataCluster)
  have heq : actual = prepared := Except.ok.inj (ha.symm.trans public_preparation_exact)
  subst actual
  exact ⟨final,hs,hr⟩

theorem positive_data_source_has_public_coupled_lifetime (a b tiles schedules) (frame : Location → Symbolic.Byte) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∃ final, Bridge.Steps HopperStage.block Tma.localShared (retryDataCandidate a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster (KernelLease.plan 2)
      ⟨prepared,fun _ => False⟩ ⟨final,Present (retryDataCandidate a b tiles schedules)⟩ ∧ Ptx.Async.Drain.Returned final := by
  have htma := (retry_data_complete_components a b tiles schedules frame ht hb).1
  obtain ⟨actual,final,ha,_,hs,_,hr,_⟩ := positive_kernel_public_coupled_return values rfl (retryDataFamily a b tiles schedules)
    ht hb htma.source htma.complete htma.histories_valid (cluster := dataCluster)
  have heq : actual = prepared := Except.ok.inj (ha.symm.trans public_preparation_exact)
  subst actual
  exact ⟨final,hs,hr⟩

theorem output_only_reservation_omits_actual_barrier :
    ¬KernelLease.Covers Tma.localShared zeroCandidate [⟨0,.write,outputStorageRegion⟩] := by
  intro hcover
  obtain ⟨index,_,hc⟩ := hcover _ _ _ (zero_initialization_uses_all_storage_bytes 0 0)
  have hi : index.val = 0 := by have := index.isLt; change index.val < 1 at this; omega
  have heq : index = ⟨0,by decide⟩ := Fin.ext hi
  subst index
  cases hc.1

theorem barrier_second_last_byte_covered : barrierStorageRegion.Contains ⟨.shared .zero,15⟩ := by simp [Regions.Region.Contains,barrierStorageRegion]
theorem barrier_adjacent_byte_excluded : ¬barrierStorageRegion.Contains ⟨.shared .zero,16⟩ := by simp [Regions.Region.Contains,barrierStorageRegion]
theorem output_adjacent_byte_excluded : ¬outputStorageRegion.Contains ⟨.global,10240⟩ := by simp [Regions.Region.Contains,outputStorageRegion]

theorem acquire_before_source_or_device_progress_rejected : Ptx.Async.await prepared 0 = .error .notComplete := by rfl

end
end Ptx.HopperKernelOwnershipTests
