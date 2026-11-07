import Ptx.Kernels.HopperDoubleBufferReplyPrefetch

/-! A three-tile source-complete candidate with nonzero, heterogeneous retries
on every tile. Tests locate actual source copies in both arenas and on reuse;
they do not assert resource/memory/tensor admission or hardware execution. -/
namespace Ptx.HopperRetryPrefetchTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def schedule (lane : Wgmma.Lane) (tile : Nat) : Nat := lane.val%3+tile+1
def query (lane : Wgmma.Lane) (tile : Nat) : Nat :=
  loopQuery 0 3 (HopperStage.leader lane) (schedule lane) (if HopperStage.leader lane then 4 else 0) tile
def waits (lane : Wgmma.Lane) : List Nat := List.ofFn (fun tile : Fin 3 => query lane tile+schedule lane tile)
def descriptors (q : Nat) : Tma.Descriptor2D :=
  if q ∈ [0,query 0 0+schedule 0 0+1,query 0 1+schedule 0 1+1] then aView 65536 3 else bView 131072 3
def replies (value : ℝ) (lane : Wgmma.Lane) : Wgmma.Oracle := {oracle 3 with
  base := {(oracle 3).base with
    wait := fun q => decide (q ∈ waits lane)
    descriptor := descriptors
    tmaBytes := fun q => List.replicate (descriptors (q-1)).bytes (.bits (byte 0))}
  matrix := fun _ _ => value}
def candidate (value : ℝ) : Unified.Candidate := replyCandidate 3 (replies value) schedule
def family (value : ℝ) : ReplySourceFamily 3 (candidate value) := {
  replies := replies value,schedules := schedule,traces := replyTrace 3 (replies value) schedule
  members := fun lane => List.mem_ofFn.mpr ⟨lane,rfl⟩
  ids := fun _ => rfl,oracles := fun _ => rfl,events := fun _ => rfl
}

theorem wait_schedule_metadata : ∀ lane : Wgmma.Lane, ∀ tile : Fin 3,
    (∀ attempt < schedule lane tile, decide (query lane tile+attempt ∈ waits lane) = false) ∧
      decide (query lane tile+schedule lane tile ∈ waits lane) = true := by decide

theorem source_well_formed (value : ℝ) (initial : Location → Symbolic.Byte) :
    Unified.WellFormed code (completeLaunch 3 initial) (candidate value) := by
  apply reply_candidate_well_formed 3 (replies value) schedule initial (by decide) (by decide)
  · intro lane _
    constructor <;> simp only [replies,List.length_replicate]
  · intro lane tile ht
    obtain ⟨hf,hs⟩ := wait_schedule_metadata lane ⟨tile,ht⟩
    refine ⟨hf,hs,?_⟩
    intro _
    constructor <;> simp only [replies,List.length_replicate] <;> congr 2

theorem source_complete (value : ℝ) : Unified.Complete (candidate value) :=
  reply_candidate_complete 3 (replies value) schedule (by decide) (by decide)

theorem dynamic_copy_indices (value : ℝ) :
    List.ofFn (fun tile : Fin 3 => (((family value).expectId tile).serial,
      ((family value).copyAId tile).issue.serial,((family value).copyBId tile).issue.serial)) =
      [(5,6,7),(10,11,12),(22,23,24)] := by rfl

theorem prefetch_query_indices (value : ℝ) :
    (replyCopyA 3 (replies value 0) (schedule 0) 1).queryBase = 6 ∧
    (replyCopyB 3 (replies value 0) (schedule 0) 1).queryBase = 8 ∧
    (replyCopyA 3 (replies value 0) (schedule 0) 2).queryBase = 15 ∧
    (replyCopyB 3 (replies value 0) (schedule 0) 2).queryBase = 17 := by
  constructor
  · rfl
  constructor
  · rfl
  exact ⟨rfl,rfl⟩

theorem actual_expectations (value : ℝ) (tile : Fin 3) :
    (candidate value).view.barrierAt ((family value).expectId tile) =
      some ⟨⟨.shared .zero,barrierAddress (stage tile)⟩,.arriveExpectTx 2304⟩ :=
  family_expect_at (family value) (source_well_formed value (fun _ => .bits (byte 0))) tile tile.isLt

theorem actual_a_copies (value : ℝ) (tile : Fin 3) :
    Tma.copyAt (candidate value).view ((family value).copyAId tile) = some (replyCopyA 3 (replies value 0) (schedule 0) tile) :=
  family_copy_a_at (family value) (source_well_formed value (fun _ => .bits (byte 0))) tile tile.isLt

theorem actual_b_copies (value : ℝ) (tile : Fin 3) :
    Tma.copyAt (candidate value).view ((family value).copyBId tile) = some (replyCopyB 3 (replies value 0) (schedule 0) tile) :=
  family_copy_b_at (family value) (source_well_formed value (fun _ => .bits (byte 0))) tile tile.isLt

theorem reused_arena_has_distinct_copies (value : ℝ) :
    (replyCopyA 3 (replies value 0) (schedule 0) 0).destination =
      (replyCopyA 3 (replies value 0) (schedule 0) 2).destination ∧
    (family value).copyAId 0 ≠ (family value).copyAId 2 := by
  constructor
  · rfl
  · intro h
    have hh := congrArg (fun id : Tma.CopyId => id.issue.serial) h
    change 6 = 23 at hh
    omega

theorem stale_zero_retry_index_rejected (value : ℝ) :
    (candidate value).eventAt ⟨(ctx 3 0).id,10⟩ ≠ some (.base (.tmaIssue (replyCopyA 3 (replies value 0) (schedule 0) 1))) := by
  have he := family_event_at (family value) (source_well_formed value (fun _ => .bits (byte 0))) 0 10 _
    (reply_complete_expect_at 3 (replies value 0) (schedule 0) 1 (by decide))
  rw [he]
  intro h
  cases h

theorem consumer_retries_shift_waits (value : ℝ) :
    ((family value).waitId 0 2).serial = 5 ∧ ((family value).waitId 1 2).serial = 16 ∧
      ((family value).waitId 2 2).serial = 28 := by exact ⟨rfl,rfl,rfl⟩

end
end Ptx.HopperRetryPrefetchTests
