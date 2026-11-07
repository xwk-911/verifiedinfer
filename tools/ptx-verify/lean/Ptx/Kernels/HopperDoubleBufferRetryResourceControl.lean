import Ptx.Kernels.HopperDoubleBufferRetryTmaControl
import Ptx.Hopper.TmaResourceRank

/-! Resource-history serialization increases the same retry-aware TMA rank.
Every failed wait is retained; notification positions are recovered from
actual copy identities. CTA/native edge checks and full admission remain
separate from these resource and implicit-access control components. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryEntryRank {tiles candidate} (family : ReplySourceFamily tiles candidate) (entry : Tma.Entry) : Nat :=
  retryTmaRank family entry.origin.node

theorem retry_failed_control_sorted {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    ((retryFailedEntries family tile).map (retryEntryRank family)).Pairwise (· < ·) := by
  rw [List.pairwise_map,retryFailedEntries,List.pairwise_flatten]
  constructor
  · intro entries he
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp he
    rw [List.pairwise_ofFn]
    intro a b hab
    change retrySourceRank family (family.failedWaitId tile lane a) < retrySourceRank family (family.failedWaitId tile lane b)
    rw [retry_failed_wait_source_rank family tile ht lane a a.isLt,retry_failed_wait_source_rank family tile ht lane b b.isLt]
    dsimp [retryFailedClock]
    omega
  · rw [List.pairwise_ofFn]
    intro left right hlt a ha b hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    change retrySourceRank family (family.failedWaitId tile left i) < retrySourceRank family (family.failedWaitId tile right j)
    rw [retry_failed_wait_source_rank family tile ht left i i.isLt,retry_failed_wait_source_rank family tile ht right j j.isLt]
    exact retry_failed_clock_lane_order family tile ht left right i j hlt i.isLt

theorem retry_successful_control_values {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (ht : tile < tiles) :
    (retrySuccessfulEntries family tile).map (retryEntryRank family) = List.ofFn (fun lane : Wgmma.Lane => retryClock family (8+10*tile) lane) := by
  simp only [retrySuccessfulEntries,List.map_ofFn,Function.comp_def,retryEntryRank,Tma.Origin.node,retryTmaRank,
    retry_successful_wait_source_rank family tile ht]

theorem retry_phase_control_values {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) :
    (retryPhaseEntries family slot phase).map (retryEntryRank family) =
      [retryUnit family*(1024*expectSerial (stageTile slot phase))]++
        (retryFailedEntries family (stageTile slot phase)).map (retryEntryRank family)++
        [retryNoticeClock family (stageTile slot phase) false,retryNoticeClock family (stageTile slot phase) true]++
        List.ofFn (fun lane : Wgmma.Lane => retryClock family (8+10*stageTile slot phase) lane) := by
  have ht := (stage_tile_in_range tiles slot phase).mpr hp
  simp only [retryPhaseEntries,List.map_append,List.map_cons,List.map_nil,retryEntryRank,Tma.Origin.node,retryTmaRank,
    retry_expect_source_rank family _ ht,retry_notification_a_rank family _ ht,retry_notification_b_rank family _ ht]
  rw [retry_successful_control_values family _ ht]

theorem retry_expect_before_failed {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) :
    retryUnit family*(1024*expectSerial tile) < retryUnit family*(1024*(7+10*tile)+128) := by
  apply Nat.mul_lt_mul_of_pos_left _ (retry_unit_pos family)
  unfold expectSerial
  split_ifs <;> omega

theorem retry_phase_control_sorted {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot) :
    ((retryPhaseEntries family slot phase).map (retryEntryRank family)).Pairwise (· < ·) := by
  have ht := (stage_tile_in_range tiles slot phase).mpr hp
  let tile := stageTile slot phase
  let failed := (retryFailedEntries family tile).map (retryEntryRank family)
  let success := List.ofFn (fun lane : Wgmma.Lane => retryClock family (8+10*tile) lane)
  have hf (x : Nat) (hx : x ∈ failed) :
      retryUnit family*(1024*expectSerial tile) < x ∧ x < retryNoticeClock family tile false := by
    obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hx
    obtain ⟨lane,attempt,rfl⟩ := (retry_failed_entry family tile entry).mp he
    change retryUnit family*(1024*expectSerial tile) < retrySourceRank family (family.failedWaitId tile lane attempt) ∧
      retrySourceRank family (family.failedWaitId tile lane attempt) < retryNoticeClock family tile false
    rw [retry_failed_wait_source_rank family tile ht lane attempt attempt.isLt]
    exact ⟨(retry_expect_before_failed family tile).trans_le (retry_failed_clock_bounds family tile ht lane attempt attempt.isLt).1,
      retry_failed_before_notice family tile ht lane attempt attempt.isLt⟩
  have he : retryUnit family*(1024*expectSerial tile) < retryNoticeClock family tile false := by
    change retryUnit family*(1024*expectSerial tile) < retryUnit family*(1024*(7+10*tile)+768)
    apply Nat.mul_lt_mul_of_pos_left _ (retry_unit_pos family)
    unfold expectSerial
    split_ifs <;> omega
  have hs (x : Nat) (hx : x ∈ success) : retryNoticeClock family tile true < x := by
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hx
    exact retry_notice_before_success family tile lane
  have hsp : success.Pairwise (· < ·) := by
    apply List.pairwise_ofFn.mpr
    intro left right hlt
    apply Nat.mul_lt_mul_of_pos_left _ (retry_unit_pos family)
    omega
  have hpre : ([retryUnit family*(1024*expectSerial tile)]++failed).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨by simp,retry_failed_control_sorted family tile ht,?_⟩
    intro x hx y hy
    rw [List.mem_singleton.mp hx]
    exact (hf y hy).1
  have hnotes : ([retryNoticeClock family tile false,retryNoticeClock family tile true]++success).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨?_,hsp,?_⟩
    · simp [retry_notice_a_before_b]
    · intro x hx y hy
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (retry_notice_a_before_b family tile).trans (hs y hy)
      · rw [List.mem_singleton.mp hx]
        exact hs y hy
  rw [retry_phase_control_values family slot phase hp]
  change (([retryUnit family*(1024*expectSerial tile)]++failed)++[retryNoticeClock family tile false,retryNoticeClock family tile true]++success).Pairwise (· < ·)
  rw [List.append_assoc]
  apply List.pairwise_append.mpr
  refine ⟨hpre,hnotes,?_⟩
  intro x hx y hy
  have hx' : x < retryNoticeClock family tile false := by
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.mem_singleton.mp hx]
      exact he
    · exact (hf x hx).2
  rcases List.mem_append.mp hy with hn | hsucc
  · rcases List.mem_cons.mp hn with rfl | hn
    · exact hx'
    · rw [List.mem_singleton.mp hn]
      exact hx'.trans (retry_notice_a_before_b family tile)
  · exact hx'.trans ((retry_notice_a_before_b family tile).trans (hs y hsucc))

theorem retry_phase_control_bounds {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot)
    (entry : Tma.Entry) (he : entry ∈ retryPhaseEntries family slot phase) :
    retryUnit family*(1024*expectSerial (stageTile slot phase)) ≤ retryEntryRank family entry ∧
      retryEntryRank family entry ≤ retryUnit family*(1024*(8+10*stageTile slot phase)+127) := by
  have ht := (stage_tile_in_range tiles slot phase).mpr hp
  have hc := retry_phase_entry_case family slot phase entry he
  cases hc with
  | expect =>
    change retryUnit family*(1024*expectSerial (stageTile slot phase)) ≤ retrySourceRank family (family.expectId (stageTile slot phase)) ∧
      retrySourceRank family (family.expectId (stageTile slot phase)) ≤ retryUnit family*(1024*(8+10*stageTile slot phase)+127)
    rw [retry_expect_source_rank family _ ht]
    refine ⟨Nat.le_refl _,?_⟩
    apply Nat.mul_le_mul_left
    unfold expectSerial
    split_ifs <;> omega
  | failed lane attempt =>
    change retryUnit family*(1024*expectSerial (stageTile slot phase)) ≤ retrySourceRank family (family.failedWaitId (stageTile slot phase) lane attempt) ∧
      retrySourceRank family (family.failedWaitId (stageTile slot phase) lane attempt) ≤ retryUnit family*(1024*(8+10*stageTile slot phase)+127)
    rw [retry_failed_wait_source_rank family _ ht lane attempt attempt.isLt]
    have hb := retry_failed_clock_bounds family _ ht lane attempt attempt.isLt
    refine ⟨(retry_expect_before_failed family _).le.trans hb.1,hb.2.le.trans ?_⟩
    apply Nat.mul_le_mul_left
    omega
  | copyA =>
    change retryUnit family*(1024*expectSerial (stageTile slot phase)) ≤ retryNotificationRank family (family.copyAId (stageTile slot phase)) ∧
      retryNotificationRank family (family.copyAId (stageTile slot phase)) ≤ retryUnit family*(1024*(8+10*stageTile slot phase)+127)
    rw [retry_notification_a_rank family _ ht]
    change retryUnit family*(1024*expectSerial _) ≤ retryUnit family*(1024*(7+10*stageTile slot phase)+768) ∧
      retryUnit family*(1024*(7+10*stageTile slot phase)+768) ≤ retryUnit family*(1024*(8+10*stageTile slot phase)+127)
    constructor
    · apply Nat.mul_le_mul_left
      unfold expectSerial
      split_ifs <;> omega
    · apply Nat.mul_le_mul_left
      omega
  | copyB =>
    change retryUnit family*(1024*expectSerial (stageTile slot phase)) ≤ retryNotificationRank family (family.copyBId (stageTile slot phase)) ∧
      retryNotificationRank family (family.copyBId (stageTile slot phase)) ≤ retryUnit family*(1024*(8+10*stageTile slot phase)+127)
    rw [retry_notification_b_rank family _ ht]
    change retryUnit family*(1024*expectSerial _) ≤ retryUnit family*(1024*(7+10*stageTile slot phase)+896) ∧
      retryUnit family*(1024*(7+10*stageTile slot phase)+896) ≤ retryUnit family*(1024*(8+10*stageTile slot phase)+127)
    constructor
    · apply Nat.mul_le_mul_left
      unfold expectSerial
      split_ifs <;> omega
    · apply Nat.mul_le_mul_left
      omega
  | wait lane =>
    change retryUnit family*(1024*expectSerial (stageTile slot phase)) ≤ retrySourceRank family (family.waitId (stageTile slot phase) lane) ∧
      retrySourceRank family (family.waitId (stageTile slot phase) lane) ≤ retryUnit family*(1024*(8+10*stageTile slot phase)+127)
    rw [retry_successful_wait_source_rank family _ ht lane]
    have hl := lane.isLt
    constructor
    · apply Nat.mul_le_mul_left
      unfold expectSerial
      split_ifs <;> omega
    · apply Nat.mul_le_mul_left
      omega

theorem retry_phases_control_sorted {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) (n : Nat) (hn : n ≤ uses tiles slot) :
    ((retryPhases family slot n).map (retryEntryRank family)).Pairwise (· < ·) := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [retryPhases,List.map_append,List.pairwise_append]
    refine ⟨ih (by omega),retry_phase_control_sorted family slot n (by omega),?_⟩
    intro left hl right hr
    obtain ⟨le,hle,rfl⟩ := List.mem_map.mp hl
    obtain ⟨re,hre,rfl⟩ := List.mem_map.mp hr
    obtain ⟨phase,hp,he⟩ := (retry_phases_entry family slot n le).mp hle
    have hb := retry_phase_control_bounds family slot phase (by omega) le he
    have hc := retry_phase_control_bounds family slot n (by omega) re hre
    have hg : retryUnit family*(1024*(8+10*stageTile slot phase)+127) < retryUnit family*(1024*expectSerial (stageTile slot n)) := by
      apply Nat.mul_lt_mul_of_pos_left _ (retry_unit_pos family)
      exact phase_control_gap (stageTile slot phase) (stageTile slot n) (by dsimp [stageTile]; omega)
    exact hb.2.trans_lt (hg.trans_le hc.1)

theorem retry_history_control_sorted {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) :
    ((retryResourceHistory family slot).map (retryEntryRank family)).Pairwise (· < ·) := by
  simp only [retryResourceHistory,List.map_append,List.map_cons,List.map_nil,retryEntryRank,Tma.Origin.node,retryTmaRank,
    retry_init_source_rank,retry_inval_source_rank]
  rw [List.pairwise_append,List.pairwise_append]
  refine ⟨⟨by simp,retry_phases_control_sorted family slot _ (Nat.le_refl _),?_⟩,by simp,?_⟩
  · intro left hl right hr
    rw [List.mem_singleton.mp hl]
    obtain ⟨entry,hm,rfl⟩ := List.mem_map.mp hr
    obtain ⟨phase,hp,he⟩ := (retry_phases_entry family slot _ entry).mp hm
    have hb := retry_phase_control_bounds family slot phase hp entry he
    have hs := slot.isLt
    have he := expect_serial_bounds (stageTile slot phase)
    have hg : retryUnit family*(1024*slot.val) < retryUnit family*(1024*expectSerial (stageTile slot phase)) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (retry_unit_pos family)
    exact hg.trans_le hb.1
  · intro left hl right hr
    rw [List.mem_singleton.mp hr]
    simp only [List.mem_append,List.mem_singleton] at hl
    rcases hl with rfl | hl
    · apply Nat.mul_lt_mul_of_pos_left _ (retry_unit_pos family)
      omega
    · obtain ⟨entry,hm,rfl⟩ := List.mem_map.mp hl
      obtain ⟨phase,hp,he⟩ := (retry_phases_entry family slot _ entry).mp hm
      have hb := retry_phase_control_bounds family slot phase hp entry he
      have ht := (stage_tile_in_range tiles slot phase).mpr hp
      have hg : retryUnit family*(1024*(8+10*stageTile slot phase)+127) < retryUnit family*(1024*(10*tiles+14+slot.val)) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (retry_unit_pos family)
      exact hb.2.trans_lt hg

theorem retry_histories_control_sorted {tiles candidate} (family : ReplySourceFamily tiles candidate) (loc : Location) :
    ((retryHistories family loc).map Tma.Entry.origin).Pairwise (fun left right => retryTmaRank family left.node < retryTmaRank family right.node) := by
  have hzero := retry_history_control_sorted family 0
  have hone := retry_history_control_sorted family 1
  simp only [List.pairwise_map,retryEntryRank] at hzero hone ⊢
  unfold retryHistories
  split_ifs
  · exact hzero
  · exact hone
  · exact List.Pairwise.nil

theorem retry_control_resource_order {tiles candidate left right} (family : ReplySourceFamily tiles candidate)
    (he : Tma.ResourceEdge (retryHistories family) left right) : retryTmaRank family left < retryTmaRank family right :=
  Tma.resource_edge_rank_of_pairwise (retry_histories_control_sorted family) he

end
end Ptx.Kernels.HopperDoubleBuffer
