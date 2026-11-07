import Ptx.Kernels.HopperDoubleBufferRetryResourceTraceCases
import Ptx.Kernels.HopperDoubleBufferResourceMembership

/-! Both membership directions between actual resource inventories and rich
retry histories. Set membership equality is not yet an inventory permutation:
origin uniqueness and source ordering are separate required proofs. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_phase_member_history {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase)
    (hp : phase < uses tiles slot) (entry : Tma.Entry) (he : entry ∈ retryPhaseEntries family slot phase) :
    entry ∈ retryResourceHistory family slot := by
  have hm := (retry_phases_entry family slot _ entry).mpr ⟨phase,hp,he⟩
  exact List.mem_append_left _ (List.mem_append_right _ hm)

theorem retry_init_member_history {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot) :
    (⟨.source (family.initId slot),.init 1⟩ : Tma.Entry) ∈ retryResourceHistory family slot := by simp [retryResourceHistory]
theorem retry_inval_member_history {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot) :
    (⟨.source (family.invalId slot),.inval⟩ : Tma.Entry) ∈ retryResourceHistory family slot := by simp [retryResourceHistory]

theorem retry_expect_member_history {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    (⟨.source (family.expectId tile),.arriveExpectTx 2304⟩ : Tma.Entry) ∈ retryResourceHistory family (stage tile) := by
  apply retry_phase_member_history family (stage tile) (tile/2) (tile_phase_in_range tiles tile ht)
  simp [retryPhaseEntries,stage_tile_index]

theorem retry_copy_a_member_history {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    (⟨.notification (family.copyAId tile),.completeTx 2048⟩ : Tma.Entry) ∈ retryResourceHistory family (stage tile) := by
  apply retry_phase_member_history family (stage tile) (tile/2) (tile_phase_in_range tiles tile ht)
  simp [retryPhaseEntries,stage_tile_index]

theorem retry_copy_b_member_history {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    (⟨.notification (family.copyBId tile),.completeTx 256⟩ : Tma.Entry) ∈ retryResourceHistory family (stage tile) := by
  apply retry_phase_member_history family (stage tile) (tile/2) (tile_phase_in_range tiles tile ht)
  simp [retryPhaseEntries,stage_tile_index]

theorem retry_wait_member_history {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) :
    (⟨.source (family.waitId tile lane),.tryWaitParity (expectedParity tile) true⟩ : Tma.Entry) ∈
      retryResourceHistory family (stage tile) := by
  apply retry_phase_member_history family (stage tile) (tile/2) (tile_phase_in_range tiles tile ht)
  simp only [retryPhaseEntries,stage_tile_index]
  apply List.mem_append_right
  exact List.mem_ofFn.mpr ⟨lane,rfl⟩

theorem retry_failed_member_history {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles)
    (lane : Wgmma.Lane) (attempt : Nat) (ha : attempt < family.schedules lane tile) :
    (⟨.source (family.failedWaitId tile lane attempt),.tryWaitParity (expectedParity tile) false⟩ : Tma.Entry) ∈
      retryResourceHistory family (stage tile) := by
  apply retry_phase_member_history family (stage tile) (tile/2) (tile_phase_in_range tiles tile ht)
  simp only [retryPhaseEntries,stage_tile_index]
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact (retry_failed_entry family tile _).mpr ⟨lane,⟨attempt,ha⟩,rfl⟩

theorem retry_actual_resource_in_history {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (origin : Tma.Origin) (event : BarrierEvent)
    (he : Tma.resourceAt Tma.localShared candidate.view origin = some event) :
    ∃ slot, event.location = dataGate slot ∧ (⟨origin,event.operation⟩ : Tma.Entry) ∈ retryResourceHistory family slot := by
  cases origin with
  | source id =>
    have hh := Unified.view_barrier_iff.mp (Hopper.barrierAt_iff.mp he)
    have hc := retry_candidate_resource_case family ht hw id (.base (.barrier event)) hh rfl
    cases hc with
    | init slot => exact ⟨slot,rfl,retry_init_member_history family slot⟩
    | inval slot => exact ⟨slot,rfl,retry_inval_member_history family slot⟩
    | expect tile hp => exact ⟨stage tile,rfl,retry_expect_member_history family tile hp⟩
    | failed tile lane attempt hp ha => exact ⟨stage tile,rfl,retry_failed_member_history family tile hp lane attempt ha⟩
    | wait tile lane hp => exact ⟨stage tile,rfl,retry_wait_member_history family tile hp lane⟩
  | notification id =>
    cases id with
    | mk issue =>
      obtain ⟨copy,hcopy,_,_⟩ := Tma.notification_has_actual_copy he
      have hh := Unified.view_tma_iff.mp (Tma.copyAt_iff.mp hcopy)
      have hc := retry_candidate_resource_case family ht hw issue (.base (.tmaIssue copy)) hh rfl
      cases hc with
      | copyA tile hp =>
        change Tma.notification Tma.localShared candidate.view (family.copyAId tile) = some event at he
        have hv := family_notification_a family hw hd tile hp
        have hresult := Option.some.inj (he.symm.trans hv)
        subst event
        exact ⟨stage tile,rfl,retry_copy_a_member_history family tile hp⟩
      | copyB tile hp =>
        change Tma.notification Tma.localShared candidate.view (family.copyBId tile) = some event at he
        have hv := family_notification_b family hw hd tile hp
        have hresult := Option.some.inj (he.symm.trans hv)
        subst event
        exact ⟨stage tile,rfl,retry_copy_b_member_history family tile hp⟩

theorem retry_inventory_in_history {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (slot) (entry : Tma.Entry)
    (he : entry ∈ Tma.inventory Tma.localShared candidate.view (dataGate slot)) : entry ∈ retryResourceHistory family slot := by
  cases entry with
  | mk origin op =>
    obtain ⟨actual,hloc,hm⟩ := retry_actual_resource_in_history family ht hw hd origin ⟨dataGate slot,op⟩ (Tma.inventory_iff.mp he)
    have hs : slot = actual := data_gate_injective hloc
    cases hs
    exact hm

theorem retry_inventory_membership_iff {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (slot) (entry : Tma.Entry) :
    entry ∈ retryResourceHistory family slot ↔ entry ∈ Tma.inventory Tma.localShared candidate.view (dataGate slot) :=
  ⟨fun he => Tma.inventory_iff.mpr (retry_history_entry_sound family hw hd slot entry he),
    retry_inventory_in_history family ht hw hd slot entry⟩

theorem retry_inventory_outside_gates {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (loc : Location) (hout : ∀ slot, loc ≠ dataGate slot) :
    Tma.inventory Tma.localShared candidate.view loc = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry he
  cases entry with
  | mk origin op =>
    obtain ⟨slot,hloc,_⟩ := retry_actual_resource_in_history family ht hw hd origin ⟨loc,op⟩ (Tma.inventory_iff.mp he)
    exact hout slot hloc

theorem completed_candidate_retry_inventory {tiles initial candidate} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) :
    ∃ family : ReplySourceFamily tiles candidate, ∀ slot entry,
      entry ∈ retryResourceHistory family slot ↔ entry ∈ Tma.inventory Tma.localShared candidate.view (dataGate slot) := by
  obtain ⟨family⟩ := completed_candidate_reply_family ht hb hw hc
  exact ⟨family,retry_inventory_membership_iff family ht hw hd⟩

end
end Ptx.Kernels.HopperDoubleBuffer
