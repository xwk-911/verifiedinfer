import Ptx.Kernels.HopperDoubleBufferRetryResourceUnique
import Ptx.Hopper.TmaSourceOrder

/-! Source program order for retry histories. Cross-phase source intervals
are disjoint even with arbitrary waits. This does not grant memory visibility
or combined control acyclicity. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem reply_initial_events_length (lane reply) :
    (replyInitialEvents lane reply).length = if HopperStage.leader lane then 8 else 2 := by
  cases hl : HopperStage.leader lane <;>
    simp [replyInitialEvents,initializationEvents,replyInitialCopies,hl]

theorem reply_start_minimum (tiles lane reply retries tile) : 2 ≤ replyTileStart tiles lane reply retries tile := by
  have hh := (reply_tile_start_strict_mono tiles lane reply retries).monotone (Nat.zero_le tile)
  have hi : 2 ≤ replyTileStart tiles lane reply retries 0 := by
    simp only [replyTileStart,replyLoopEvents,loopEvents,List.length_nil,Nat.add_zero,reply_initial_events_length]
    cases HopperStage.leader lane <;> decide
  omega

theorem reply_expect_before_start (tiles reply retries tile) :
    (replyExpectId tiles reply retries tile).serial < replyTileStart tiles 0 reply retries tile := by
  cases tile with
  | zero => change 5 < 8; decide
  | succ tile =>
    simp only [replyExpectId,replyPrefetchId,reply_tile_start_succ]
    omega

theorem retry_wait_source_bounds {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane)
    (attempt : Nat) (ha : attempt ≤ family.schedules lane tile) :
    2 ≤ (family.failedWaitId tile lane attempt).serial ∧
    (family.failedWaitId tile lane attempt).serial < replyTileStart tiles lane (family.replies lane) (family.schedules lane) (tile+1) ∧
    (0 < tile → replyTileStart tiles lane (family.replies lane) (family.schedules lane) (tile-1) ≤ (family.failedWaitId tile lane attempt).serial) := by
  have hm := reply_start_minimum tiles lane (family.replies lane) (family.schedules lane) tile
  have hu := (reply_wait_interval tiles lane (family.replies lane) (family.schedules lane) tile attempt ha).2
  have hl := (reply_tile_start_strict_mono tiles lane (family.replies lane) (family.schedules lane)).monotone (Nat.sub_le tile 1)
  change 2 ≤ replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+attempt ∧ _
  refine ⟨by omega,hu,?_⟩
  intro _
  change _ ≤ replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+attempt
  omega

theorem retry_entry_source_bounds {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (entry : Tma.Entry)
    (hc : RetryPhaseEntry family tile entry) (id : Ptx.Event.EventId) (ho : entry.origin = .source id) :
    ∃ lane : Wgmma.Lane, id.thread = (ctx tiles lane).id ∧ 2 ≤ id.serial ∧
      id.serial < replyTileStart tiles lane (family.replies lane) (family.schedules lane) (tile+1) ∧
      (0 < tile → replyTileStart tiles lane (family.replies lane) (family.schedules lane) (tile-1) ≤ id.serial) := by
  cases hc with
  | expect =>
    have hid := (Tma.Origin.source.inj ho).symm
    rw [hid]
    have hu := reply_expect_before_start tiles (family.replies 0) (family.schedules 0) tile
    have hm := reply_tile_start_strict_mono tiles 0 (family.replies 0) (family.schedules 0) (Nat.lt_succ_self tile)
    cases tile with
    | zero => exact ⟨0,rfl,by change 2 ≤ 5; decide,hu.trans hm,by omega⟩
    | succ tile =>
      have hmin := reply_start_minimum tiles 0 (family.replies 0) (family.schedules 0) tile
      refine ⟨0,rfl,?_,hu.trans hm,?_⟩
      · change 2 ≤ replyTileStart tiles 0 (family.replies 0) (family.schedules 0) tile+family.schedules 0 tile+1+0
        omega
      · intro _
        change replyTileStart tiles 0 (family.replies 0) (family.schedules 0) tile ≤
          replyTileStart tiles 0 (family.replies 0) (family.schedules 0) tile+family.schedules 0 tile+1+0
        omega
  | failed lane attempt =>
    have hid := (Tma.Origin.source.inj ho).symm
    rw [hid]
    exact ⟨lane,rfl,retry_wait_source_bounds family tile lane attempt (Nat.le_of_lt attempt.isLt)⟩
  | copyA => cases ho
  | copyB => cases ho
  | wait lane =>
    have hid := (Tma.Origin.source.inj ho).symm
    rw [hid]
    exact ⟨lane,rfl,retry_wait_source_bounds family tile lane (family.schedules lane tile) (Nat.le_refl _)⟩

theorem retry_cross_phase_forward {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot left right)
    (hp : left < right) (a b : Tma.Entry) (ha : a ∈ retryPhaseEntries family slot left) (hb : b ∈ retryPhaseEntries family slot right) :
    Tma.SourceForward a b := by
  cases hoa : a.origin with
  | notification copy => simp [Tma.SourceForward,hoa]
  | source ida =>
    cases hob : b.origin with
    | notification copy => simp [Tma.SourceForward,hoa,hob]
    | source idb =>
      simp only [Tma.SourceForward,hoa,hob]
      intro he
      obtain ⟨la,hla,_,hua,_⟩ := retry_entry_source_bounds family _ a (retry_phase_entry_case family slot left a ha) ida hoa
      obtain ⟨lb,hlb,_,_,hlow⟩ := retry_entry_source_bounds family _ b (retry_phase_entry_case family slot right b hb) idb hob
      have hab : la = lb := resource_ctx_injective tiles (hla.symm.trans (he.trans hlb))
      subst lb
      have htile : stageTile slot left+1 ≤ stageTile slot right-1 := by dsimp [stageTile]; omega
      have hpos : 0 < stageTile slot right := by dsimp [stageTile]; omega
      have hm := (reply_tile_start_strict_mono tiles la (family.replies la) (family.schedules la)).monotone htile
      have hl := hlow hpos
      omega

theorem retry_failed_entries_forward {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) :
    (retryFailedEntries family tile).Pairwise Tma.SourceForward := by
  rw [retryFailedEntries,List.pairwise_flatten]
  constructor
  · intro entries he
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp he
    rw [List.pairwise_ofFn]
    intro a b hab _
    change replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+a.val <
      replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+b.val
    exact Nat.add_lt_add_left hab _
  · rw [List.pairwise_ofFn]
    intro left right hlt a ha b hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    intro he
    have hl : left = right := resource_ctx_injective tiles he
    have hh := congrArg Fin.val hl
    omega

theorem retry_successful_entries_forward {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) :
    (retrySuccessfulEntries family tile).Pairwise Tma.SourceForward := by
  rw [retrySuccessfulEntries,List.pairwise_ofFn]
  intro left right hlt he
  have hl : left = right := resource_ctx_injective tiles he
  have hh := congrArg Fin.val hl
  omega

theorem retry_expect_forward_wait {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (lane : Wgmma.Lane)
    (attempt : Nat) (answer : Bool) :
    Tma.SourceForward ⟨.source (family.expectId tile),.arriveExpectTx 2304⟩
      ⟨.source (family.failedWaitId tile lane attempt),.tryWaitParity (expectedParity tile) answer⟩ := by
  intro he
  have hid : (family.expectId tile).thread = (ctx tiles 0).id := by cases tile <;> rfl
  have hl : (0 : Wgmma.Lane) = lane := resource_ctx_injective tiles (hid.symm.trans he)
  subst lane
  have hh := reply_expect_before_start tiles (family.replies 0) (family.schedules 0) tile
  change (replyExpectId tiles (family.replies 0) (family.schedules 0) tile).serial <
    replyTileStart tiles 0 (family.replies 0) (family.schedules 0) tile+attempt
  omega

theorem retry_phase_entries_forward {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) :
    (retryPhaseEntries family slot phase).Pairwise Tma.SourceForward := by
  rw [retryPhaseEntries,List.pairwise_append,List.pairwise_append,List.pairwise_append]
  refine ⟨⟨⟨by simp,retry_failed_entries_forward family _,?_⟩,?_,?_⟩,retry_successful_entries_forward family _,?_⟩
  · intro a ha b hb
    simp only [List.mem_singleton] at ha
    rw [ha]
    obtain ⟨lane,attempt,rfl⟩ := (retry_failed_entry family _ _).mp hb
    exact retry_expect_forward_wait family _ lane attempt false
  · simp [Tma.SourceForward]
  · intro a _ b hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl <;> cases hoa : a.origin <;> simp [Tma.SourceForward,hoa]
  · intro a ha b hb
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hb
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with (rfl | ha) | (rfl | rfl)
    · exact retry_expect_forward_wait family _ lane _ true
    · obtain ⟨other,attempt,rfl⟩ := (retry_failed_entry family _ _).mp ha
      intro he
      have hl : other = lane := resource_ctx_injective tiles he
      subst other
      change replyTileStart tiles lane (family.replies lane) (family.schedules lane) (stageTile slot phase)+attempt.val <
        replyTileStart tiles lane (family.replies lane) (family.schedules lane) (stageTile slot phase)+family.schedules lane (stageTile slot phase)
      exact Nat.add_lt_add_left attempt.isLt _
    · trivial
    · trivial

theorem retry_phases_entries_forward {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot n) :
    (retryPhases family slot n).Pairwise Tma.SourceForward := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [retryPhases,List.pairwise_append]
    refine ⟨ih,retry_phase_entries_forward family slot n,?_⟩
    intro a ha b hb
    obtain ⟨phase,hp,ha⟩ := (retry_phases_entry family slot n a).mp ha
    exact retry_cross_phase_forward family slot phase n hp a b ha hb

theorem retry_init_forward_phase {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (entry : Tma.Entry)
    (he : entry ∈ retryPhaseEntries family slot phase) :
    Tma.SourceForward ⟨.source (family.initId slot),.init 1⟩ entry := by
  cases ho : entry.origin with
  | notification copy => simp [Tma.SourceForward,ho]
  | source id =>
    simp only [Tma.SourceForward,ho]
    intro _
    obtain ⟨_,_,hm,_,_⟩ := retry_entry_source_bounds family _ entry (retry_phase_entry_case family slot phase entry he) id ho
    have hs := slot.isLt
    change slot.val < id.serial
    omega

theorem retry_phase_forward_inval {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot phase) (hp : phase < uses tiles slot)
    (entry : Tma.Entry) (he : entry ∈ retryPhaseEntries family slot phase) :
    Tma.SourceForward entry ⟨.source (family.invalId slot),.inval⟩ := by
  cases ho : entry.origin with
  | notification copy => simp [Tma.SourceForward,ho]
  | source id =>
    simp only [Tma.SourceForward,ho]
    intro hid
    obtain ⟨lane,hl,_,hu,_⟩ := retry_entry_source_bounds family _ entry (retry_phase_entry_case family slot phase entry he) id ho
    have heq : lane = 0 := resource_ctx_injective tiles (hl.symm.trans hid)
    subst lane
    have ht := (stage_tile_in_range tiles slot phase).mpr hp
    have hm := (reply_tile_start_strict_mono tiles 0 (family.replies 0) (family.schedules 0)).monotone (show stageTile slot phase+1 ≤ tiles by omega)
    change id.serial < replyTileStart tiles 0 (family.replies 0) (family.schedules 0) tiles+6+slot.val
    omega

theorem retry_history_entries_forward {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot) :
    (retryResourceHistory family slot).Pairwise Tma.SourceForward := by
  rw [retryResourceHistory,List.pairwise_append,List.pairwise_append]
  refine ⟨⟨by simp,retry_phases_entries_forward family slot _,?_⟩,by simp,?_⟩
  · intro a ha b hb
    simp only [List.mem_singleton] at ha
    rw [ha]
    obtain ⟨phase,_,hb⟩ := (retry_phases_entry family slot _ b).mp hb
    exact retry_init_forward_phase family slot phase b hb
  · intro a ha b hb
    simp only [List.mem_singleton] at hb
    rw [hb]
    simp only [List.mem_append,List.mem_singleton] at ha
    rcases ha with rfl | ha
    · intro _
      change slot.val < replyTileStart tiles 0 (family.replies 0) (family.schedules 0) tiles+6+slot.val
      omega
    · obtain ⟨phase,hp,ha⟩ := (retry_phases_entry family slot _ a).mp ha
      exact retry_phase_forward_inval family slot phase hp a ha

theorem retry_history_source_order {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (slot) : Tma.SourceOrder (retryResourceHistory family slot) :=
  Tma.source_order_of_pairwise (retry_history_origins_unique family hw hd slot) (retry_history_entries_forward family slot)

end
end Ptx.Kernels.HopperDoubleBuffer
