import Ptx.Kernels.HopperDoubleBufferRetryResourceIdentities
import Ptx.Hopper.TmaInventoryUnique

/-! No duplicate entries or actual origins in rich retry histories. Inventory
permutations are derived from uniqueness and both membership directions;
source order/control admission are separate. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

inductive RetryPhaseEntry {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) : Tma.Entry → Prop
  | expect : RetryPhaseEntry family tile ⟨.source (family.expectId tile),.arriveExpectTx 2304⟩
  | failed (lane : Wgmma.Lane) (attempt : Fin (family.schedules lane tile)) :
      RetryPhaseEntry family tile ⟨.source (family.failedWaitId tile lane attempt),.tryWaitParity (expectedParity tile) false⟩
  | copyA : RetryPhaseEntry family tile ⟨.notification (family.copyAId tile),.completeTx 2048⟩
  | copyB : RetryPhaseEntry family tile ⟨.notification (family.copyBId tile),.completeTx 256⟩
  | wait (lane : Wgmma.Lane) : RetryPhaseEntry family tile ⟨.source (family.waitId tile lane),.tryWaitParity (expectedParity tile) true⟩

theorem retry_phase_entry_case {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (entry : Tma.Entry)
    (he : entry ∈ retryPhaseEntries family slot phase) : RetryPhaseEntry family (stageTile slot phase) entry := by
  simp only [retryPhaseEntries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with ((rfl | he) | (rfl | rfl)) | he
  · exact .expect
  · obtain ⟨lane,attempt,rfl⟩ := (retry_failed_entry family _ _).mp he
    exact .failed lane attempt
  · exact .copyA
  · exact .copyB
  · obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp he
    exact .wait lane

theorem retry_phase_entry_tile_unique {tiles candidate} (family : ReplySourceFamily tiles candidate) {left right entry}
    (hl : RetryPhaseEntry family left entry) (hr : RetryPhaseEntry family right entry) : left = right := by
  have handle (other : Tma.Entry) (hx : RetryPhaseEntry family right other) (he : entry = other) : left = right := by
    cases hl <;> cases hx <;> simp at he
    case expect.expect => exact family_expect_tile_injective family he
    case failed.failed lane attempt lane' attempt' =>
      exact (family_wait_endpoint_injective family left right lane lane' attempt attempt'
        (Nat.le_of_lt attempt.isLt) (Nat.le_of_lt attempt'.isLt) he.1).1
    case copyA.copyA => exact family_copy_a_tile_injective family he
    case copyB.copyB => exact family_copy_b_tile_injective family he
    case wait.wait lane lane' =>
      exact (family_wait_endpoint_injective family left right lane lane' _ _ (Nat.le_refl _) (Nat.le_refl _) he.1).1
  exact handle entry hr rfl

theorem retry_failed_entries_nodup {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) :
    (retryFailedEntries family tile).Nodup := by
  rw [retryFailedEntries,List.nodup_flatten]
  constructor
  · intro entries he
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp he
    apply List.nodup_ofFn.mpr
    intro a b he
    have hi := (family_wait_endpoint_injective family tile tile lane lane a b
      (Nat.le_of_lt a.isLt) (Nat.le_of_lt b.isLt)
      (Tma.Origin.source.inj (congrArg Tma.Entry.origin he))).2.2
    exact Fin.ext hi
  · rw [List.pairwise_ofFn]
    intro left right hlt
    apply List.disjoint_left.mpr
    intro entry hl hr
    obtain ⟨a,ha⟩ := List.mem_ofFn.mp hl
    obtain ⟨b,hb⟩ := List.mem_ofFn.mp hr
    have he := ha.trans hb.symm
    have hi := (family_wait_endpoint_injective family tile tile left right a b
      (Nat.le_of_lt a.isLt) (Nat.le_of_lt b.isLt)
      (Tma.Origin.source.inj (congrArg Tma.Entry.origin he))).2.1
    have hh := congrArg Fin.val hi
    omega

theorem retry_successful_entries_nodup {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) :
    (retrySuccessfulEntries family tile).Nodup := by
  apply List.nodup_ofFn.mpr
  intro left right he
  exact (family_wait_endpoint_injective family tile tile left right _ _ (Nat.le_refl _) (Nat.le_refl _)
    (Tma.Origin.source.inj (congrArg Tma.Entry.origin he))).2.1

theorem retry_phase_entries_nodup {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) :
    (retryPhaseEntries family slot phase).Nodup := by
  rw [retryPhaseEntries,List.nodup_append,List.nodup_append,List.nodup_append]
  refine ⟨⟨⟨by simp,retry_failed_entries_nodup family _,?_⟩,by simp,?_⟩,retry_successful_entries_nodup family _,?_⟩
  · intro a ha b hb he
    simp only [List.mem_singleton] at ha
    rw [ha] at he
    obtain ⟨lane,attempt,rfl⟩ := (retry_failed_entry family _ _).mp hb
    have hh := congrArg Tma.Entry.operation he
    cases hh
  · intro a ha b hb he
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | rfl <;> cases congrArg Tma.Entry.operation he
    · obtain ⟨lane,attempt,rfl⟩ := (retry_failed_entry family _ _).mp ha
      rcases hb with rfl | rfl <;> cases congrArg Tma.Entry.operation he
  · intro a ha b hb he
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hb
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with (rfl | ha) | (rfl | rfl)
    · cases congrArg Tma.Entry.operation he
    · obtain ⟨other,attempt,rfl⟩ := (retry_failed_entry family _ _).mp ha
      have hh := congrArg Tma.Entry.operation he
      cases hh
    · cases congrArg Tma.Entry.operation he
    · cases congrArg Tma.Entry.operation he

theorem retry_phases_entries_nodup {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot n) :
    (retryPhases family slot n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
    rw [retryPhases,List.nodup_append]
    refine ⟨ih,retry_phase_entries_nodup family slot n,?_⟩
    intro a ha b hb he
    subst b
    obtain ⟨phase,hp,ha⟩ := (retry_phases_entry family slot n a).mp ha
    have hh := retry_phase_entry_tile_unique family (retry_phase_entry_case family slot phase a ha) (retry_phase_entry_case family slot n a hb)
    dsimp [stageTile] at hh
    omega

theorem retry_phases_exclude_endpoints {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot n) (entry : Tma.Entry)
    (he : entry ∈ retryPhases family slot n) : entry.operation ≠ .init 1 ∧ entry.operation ≠ .inval := by
  obtain ⟨phase,_,he⟩ := (retry_phases_entry family slot n entry).mp he
  have hc := retry_phase_entry_case family slot phase entry he
  cases hc <;> simp

theorem retry_history_entries_nodup {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot) :
    (retryResourceHistory family slot).Nodup := by
  rw [retryResourceHistory,List.nodup_append,List.nodup_append]
  refine ⟨⟨by simp,retry_phases_entries_nodup family slot _,?_⟩,by simp,?_⟩
  · intro a ha b hb he
    simp only [List.mem_singleton] at ha
    rw [ha] at he
    exact (retry_phases_exclude_endpoints family slot _ b hb).1 (congrArg Tma.Entry.operation he).symm
  · intro a ha b hb he
    simp only [List.mem_singleton] at hb
    rw [hb] at he
    simp only [List.mem_append,List.mem_singleton] at ha
    rcases ha with rfl | ha
    · cases congrArg Tma.Entry.operation he
    · exact (retry_phases_exclude_endpoints family slot _ a ha).2 (congrArg Tma.Entry.operation he)

theorem retry_history_origins_unique {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (slot) :
    ((retryResourceHistory family slot).map Tma.Entry.origin).Nodup := by
  apply List.Nodup.map_on (d := retry_history_entries_nodup family slot)
  intro a ha b hb he
  have hsa := retry_history_entry_sound family hw hd slot a ha
  have hsb := retry_history_entry_sound family hw hd slot b hb
  rw [he] at hsa
  have hop := congrArg BarrierEvent.operation (Option.some.inj (hsa.symm.trans hsb))
  cases a
  cases b
  simp_all only

theorem retry_candidate_inventory_unique {tiles initial candidate}
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (loc : Location) :
    (Tma.inventory Tma.localShared candidate.view loc).Nodup := by
  apply Tma.inventory_unique
  simpa only [Unified.Candidate.view,List.map_map,Function.comp_def,Unified.ThreadTrace.view] using hw.2.1

theorem retry_history_exhaustive {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (slot) :
    (retryResourceHistory family slot).Perm (Tma.inventory Tma.localShared candidate.view (dataGate slot)) := by
  apply (List.perm_ext_iff_of_nodup (retry_history_entries_nodup family slot)
    (retry_candidate_inventory_unique hw (dataGate slot))).mpr
  exact retry_inventory_membership_iff family ht hw hd slot

end
end Ptx.Kernels.HopperDoubleBuffer
