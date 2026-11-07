import Ptx.Hopper.KernelLease
import Ptx.Hopper.RegionComposition
import Ptx.Kernels.HopperDoubleBufferRetryResourceMembership
import Ptx.Kernels.HopperDoubleBufferProgress
import Ptx.Kernels.HopperDoubleBufferZeroExecution

/-! Exhaustive ordinary-source and mbarrier-storage lifetime coverage for the
fixed output geometry. Zero K still initializes and invalidates both barriers;
it needs the output and barrier reservations but no descriptor/input buffers.
The older async-region certificate separately covers TMA/native byte uses.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def outputStorageRegion : Regions.Region := ⟨⟨.global,8192⟩,2048⟩
def barrierStorageRegion : Regions.Region := ⟨⟨.shared .zero,0⟩,16⟩
def kernelReservations : List KernelLease.Reservation :=
  [⟨0,.write,outputStorageRegion⟩,⟨1,.write,barrierStorageRegion⟩]
def kernelStorageLayout : Regions.Layout := fun bid => [outputStorageRegion,barrierStorageRegion][bid]?

theorem kernel_reservations_valid (values : List Nat) (hv : values.length = 2) : KernelLease.Valid values kernelReservations := by
  intro resource hm
  simp only [kernelReservations,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl <;> simp [hv]

theorem kernel_reservations_mapped : KernelLease.Mapped kernelStorageLayout kernelReservations := by
  intro resource hm
  simp only [kernelReservations,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl <;> rfl

theorem kernel_storage_separated : Regions.Separated kernelStorageLayout := by
  apply Regions.separated_of_pairwise
  simp [Regions.Region.Disjoint,outputStorageRegion,barrierStorageRegion]

theorem ordinary_write_in_output {tiles initial candidate id loc value} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (he : Unified.writeByte Tma.localShared Access.globalDescriptor candidate (.base (.tma (.source id))) loc = some value) :
    outputStorageRegion.Contains loc := by
  have ha : Unified.Accesses Tma.localShared Access.globalDescriptor candidate (.base (.tma (.source id))) loc := .inr (by rw [he]; rfl)
  obtain ⟨base,size,hf⟩ := Unified.access_footprint_exists ha
  have hr := candidate_source_word_region hb hw hc hf
  have hbounds := Unified.access_footprint_bounds ha hf
  change loc.space = .global ∧ 8192 ≤ loc.address ∧ loc.address < 8192+2048
  rcases hr with ⟨hspace,rfl,hlo,hhi,_⟩
  exact ⟨hbounds.1.symm.trans hspace,by omega,by omega⟩

theorem barrier_storage_contains (slot : Stage) {offset : Nat} (ho : offset < 8) :
    barrierStorageRegion.Contains ((dataGate slot).add offset) := by
  have hs := slot.isLt
  simp only [Regions.Region.Contains,barrierStorageRegion,dataGate,barrierAddress,Location.add]
  exact ⟨trivial,by omega,by omega⟩

theorem positive_kernel_use_coverage {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) :
    KernelLease.Covers Tma.localShared candidate kernelReservations := by
  intro control loc mode hu
  cases hu with
  | @read id kind loc value he hr =>
    have hn := candidate_ordinary_read_none hb hw hc id loc
    simp [Access.readByte,Access.kind,he,hr] at hn
  | @write id kind loc value he hwrite =>
    have hx : Unified.writeByte Tma.localShared Access.globalDescriptor candidate (.base (.tma (.source id))) loc = some value := by
      simpa [Unified.writeByte,Unified.kind,Access.kind,he] using hwrite
    exact ⟨⟨0,by decide⟩,rfl,ordinary_write_in_output hb hw hc hx⟩
  | @resource origin event offset he ho =>
    obtain ⟨slot,hgate,_⟩ := retry_actual_resource_in_history family ht hw hd origin event he
    exact ⟨⟨1,by decide⟩,rfl,by
      change barrierStorageRegion.Contains (event.location.add offset)
      rw [hgate]
      exact barrier_storage_contains slot ho⟩

theorem zero_kernel_use_coverage {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    KernelLease.Covers Tma.localShared candidate kernelReservations := by
  intro control loc mode hu
  cases hu with
  | @read id kind loc value he hr =>
    have hn := candidate_ordinary_read_none (by decide) hw hc id loc
    simp [Access.readByte,Access.kind,he,hr] at hn
  | @write id kind loc value he hwrite =>
    have hx : Unified.writeByte Tma.localShared Access.globalDescriptor candidate (.base (.tma (.source id))) loc = some value := by
      simpa [Unified.writeByte,Unified.kind,Access.kind,he] using hwrite
    exact ⟨⟨0,by decide⟩,rfl,ordinary_write_in_output (by decide) hw hc hx⟩
  | @resource origin event offset he ho =>
    rw [Tma.resource_at_lookup_eq (Unified.view_lookup_eq (completed_zero_event_lookup hw hc)) Tma.localShared] at he
    obtain ⟨slot,hgate,_⟩ := data_actual_resource_in_history (fun _ _ => 0) (fun _ _ => 0) 0 (by decide) origin event he
    exact ⟨⟨1,by decide⟩,rfl,by
      change barrierStorageRegion.Contains (event.location.add offset)
      rw [hgate]
      exact barrier_storage_contains slot ho⟩

theorem zero_kernel_public_pending_rejected {values prepared candidate initial histories cluster state bid region control loc mode}
    (hv : values.length = 2)
    (hprep : Ptx.Async.run (Ptx.Async.initial 1 values) (KernelLease.prepareActions kernelReservations) = .ok prepared)
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (hs : Bridge.Steps HopperStage.block Tma.localShared candidate histories cluster (KernelLease.plan 2)
      ⟨prepared,fun _ => False⟩ state)
    (hu : KernelUse Tma.localShared candidate control loc mode) (hp : ¬state.done control)
    (hl : kernelStorageLayout bid = some region) (hr : region.Contains loc) :
    Ptx.Async.reclaim state.protocol bid = .error .outstandingLoan ∧
      ∀ value, Ptx.Async.hostWrite state.protocol bid value = .error .outstandingLoan :=
  KernelLease.public_pending_region_reclaim_write_rejected (kernel_reservations_valid values hv) hprep hs
    kernel_reservations_mapped kernel_storage_separated (zero_kernel_use_coverage hw hc) hu hp hl hr

theorem positive_kernel_public_pending_rejected {tiles values prepared candidate initial histories cluster state bid region control loc mode}
    (family : ReplySourceFamily tiles candidate) (hv : values.length = 2) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hprep : Ptx.Async.run (Ptx.Async.initial 1 values) (KernelLease.prepareActions kernelReservations) = .ok prepared)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hs : Bridge.Steps HopperStage.block Tma.localShared candidate histories cluster (KernelLease.plan 2)
      ⟨prepared,fun _ => False⟩ state)
    (hu : KernelUse Tma.localShared candidate control loc mode) (hp : ¬state.done control)
    (hl : kernelStorageLayout bid = some region) (hr : region.Contains loc) :
    Ptx.Async.reclaim state.protocol bid = .error .outstandingLoan ∧
      ∀ value, Ptx.Async.hostWrite state.protocol bid value = .error .outstandingLoan :=
  KernelLease.public_pending_region_reclaim_write_rejected (kernel_reservations_valid values hv) hprep hs
    kernel_reservations_mapped kernel_storage_separated (positive_kernel_use_coverage family ht hb hw hc hd) hu hp hl hr

theorem zero_kernel_public_coupled_return (values : List Nat) (hv : values.length = 2) {initial candidate} {cluster : Access.ClusterScope}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    ∃ prepared final,
      Ptx.Async.run (Ptx.Async.initial 1 values) (KernelLease.prepareActions kernelReservations) = .ok prepared ∧
      Regions.Borrowed (KernelLease.bindings kernelReservations) prepared ∧
      Bridge.Steps HopperStage.block Tma.localShared candidate zeroHistories cluster (KernelLease.plan 2)
        ⟨prepared,fun _ => False⟩ ⟨final,Present candidate⟩ ∧
      Ptx.Async.run prepared (KernelLease.returnActions kernelReservations) = .ok final ∧
      Ptx.Async.Drain.Returned final ∧ Ptx.Async.Preparation.Live final ∧ final.buffers.length = values.length := by
  exact KernelLease.coupled_return_exists values kernelReservations (kernel_reservations_valid values hv) hc
    (full_prefix_reached (completed_zero_history_valid hw hc) (dataNativeControlRank 0)
      (fun _ _ => completed_zero_control_rank hw hc))

theorem positive_kernel_public_coupled_return (values : List Nat) (hv : values.length = 2)
    {tiles initial candidate} {cluster : Access.ClusterScope} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hc : Unified.Complete candidate) (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (retryHistories family loc)) :
    ∃ prepared final,
      Ptx.Async.run (Ptx.Async.initial 1 values) (KernelLease.prepareActions kernelReservations) = .ok prepared ∧
      Regions.Borrowed (KernelLease.bindings kernelReservations) prepared ∧
      Bridge.Steps HopperStage.block Tma.localShared candidate (retryHistories family) cluster (KernelLease.plan 2)
        ⟨prepared,fun _ => False⟩ ⟨final,Present candidate⟩ ∧
      Ptx.Async.run prepared (KernelLease.returnActions kernelReservations) = .ok final ∧
      Ptx.Async.Drain.Returned final ∧ Ptx.Async.Preparation.Live final ∧ final.buffers.length = values.length :=
  KernelLease.coupled_return_exists values kernelReservations (kernel_reservations_valid values hv) hc
    (retry_family_full_prefix family ht hb hw hh)

end
end Ptx.Kernels.HopperDoubleBuffer
