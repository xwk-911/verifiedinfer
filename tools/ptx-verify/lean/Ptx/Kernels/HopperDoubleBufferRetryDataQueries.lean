import Ptx.Kernels.HopperDoubleBufferRetryArithmetic

/-! Pure query schedules for independently constructed retry data replies.
Freshness is proved from the source query recurrence, without inspecting any
real-valued reply or assuming a memory/tensor execution. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryDataQuery (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) (lane : Wgmma.Lane) (tile : Nat) : Nat :=
  loopQuery 0 tiles (HopperStage.leader lane) (schedules lane) (initialQuery (HopperStage.leader lane)) tile
def retryDataWaitQuery (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) (lane : Wgmma.Lane) (tile : Nat) : Nat :=
  retryDataQuery tiles schedules lane tile+schedules lane tile
def retryDataNativeQuery (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) (lane : Wgmma.Lane) (tile : Nat) : Nat :=
  retryDataWaitQuery tiles schedules lane tile+1+(if needsPrefetch tile tiles (HopperStage.leader lane) then 4 else 0)
def retryDataCopyQuery (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) (tile : Nat) (part : Fin 2) : Nat :=
  match tile with
  | 0 => 2*part.val
  | tile+1 => retryDataWaitQuery tiles schedules 0 tile+1+2*part.val

theorem retry_data_query_step (tiles schedules lane tile) :
    retryDataQuery tiles schedules lane (tile+1) = retryDataNativeQuery tiles schedules lane tile+2 := by
  simp only [retryDataQuery,loopQuery,retryDataNativeQuery,retryDataWaitQuery,Nat.zero_add]

theorem retry_data_wait_interval_separation (tiles schedules lane left right) (hlr : left < right) :
    retryDataWaitQuery tiles schedules lane left < retryDataQuery tiles schedules lane right := by
  simpa only [retryDataWaitQuery,retryDataQuery,Nat.zero_add] using
    wait_query_intervals_disjoint 0 tiles (HopperStage.leader lane) (schedules lane)
      (initialQuery (HopperStage.leader lane)) left right hlr

theorem retry_data_failed_not_success (tiles schedules lane tile attempt) (ha : attempt < schedules lane tile) :
    ∀ other, retryDataQuery tiles schedules lane tile+attempt ≠ retryDataWaitQuery tiles schedules lane other := by
  intro other he
  rcases lt_trichotomy other tile with hold | rfl | hnext
  · have h := retry_data_wait_interval_separation tiles schedules lane other tile hold
    omega
  · unfold retryDataWaitQuery at he
    omega
  · have h := retry_data_wait_interval_separation tiles schedules lane tile other hnext
    unfold retryDataWaitQuery at he h
    omega

theorem retry_data_native_query_strict (tiles schedules lane) : StrictMono (retryDataNativeQuery tiles schedules lane) := by
  apply strictMono_nat_of_lt_succ
  intro tile
  have hs := retry_data_query_step tiles schedules lane tile
  unfold retryDataNativeQuery retryDataWaitQuery at hs ⊢
  omega

theorem retry_data_copy_query_pair (tiles schedules tile) :
    retryDataCopyQuery tiles schedules tile 0 < retryDataCopyQuery tiles schedules tile 1 := by
  cases tile <;> simp only [retryDataCopyQuery,Fin.val_zero,Fin.val_one] <;> omega

theorem retry_data_copy_query_gap (tiles schedules tile) :
    retryDataCopyQuery tiles schedules tile 1 < retryDataCopyQuery tiles schedules (tile+1) 0 := by
  cases tile with
  | zero =>
    change 2 < 4+schedules 0 0+1+2*0
    omega
  | succ tile =>
    have hs := loopQuery_step_bound 0 tiles (HopperStage.leader 0) (schedules 0)
      (initialQuery (HopperStage.leader 0)) tile
    simp only [Nat.zero_add] at hs
    change retryDataQuery tiles schedules 0 tile+schedules 0 tile+3 ≤ retryDataQuery tiles schedules 0 (tile+1) at hs
    simp only [retryDataCopyQuery,retryDataWaitQuery,Fin.val_zero,Fin.val_one]
    omega

theorem retry_data_copy_a_strict (tiles schedules) : StrictMono (fun tile => retryDataCopyQuery tiles schedules tile 0) := by
  apply strictMono_nat_of_lt_succ
  intro tile
  exact (retry_data_copy_query_pair tiles schedules tile).trans (retry_data_copy_query_gap tiles schedules tile)

theorem retry_data_copy_part_bounds (tiles schedules tile) (part : Fin 2) :
    retryDataCopyQuery tiles schedules tile 0 ≤ retryDataCopyQuery tiles schedules tile part ∧
      retryDataCopyQuery tiles schedules tile part ≤ retryDataCopyQuery tiles schedules tile 1 := by
  have hp := retry_data_copy_query_pair tiles schedules tile
  fin_cases part
  · change retryDataCopyQuery tiles schedules tile 0 ≤ retryDataCopyQuery tiles schedules tile 0 ∧
      retryDataCopyQuery tiles schedules tile 0 ≤ retryDataCopyQuery tiles schedules tile 1
    exact ⟨Nat.le_refl _,hp.le⟩
  · change retryDataCopyQuery tiles schedules tile 0 ≤ retryDataCopyQuery tiles schedules tile 1 ∧
      retryDataCopyQuery tiles schedules tile 1 ≤ retryDataCopyQuery tiles schedules tile 1
    exact ⟨hp.le,Nat.le_refl _⟩

theorem retry_data_copy_query_order (tiles schedules left right) (hlr : left < right) (a b : Fin 2) :
    retryDataCopyQuery tiles schedules left a < retryDataCopyQuery tiles schedules right b := by
  have hl := (retry_data_copy_part_bounds tiles schedules left a).2
  have hg := retry_data_copy_query_gap tiles schedules left
  have hm := (retry_data_copy_a_strict tiles schedules).monotone (show left+1 ≤ right by omega)
  have hr := (retry_data_copy_part_bounds tiles schedules right b).1
  omega

theorem retry_data_copy_query_identity {tiles schedules left right} {a b : Fin 2}
    (he : retryDataCopyQuery tiles schedules left a = retryDataCopyQuery tiles schedules right b) : left = right ∧ a = b := by
  have ht : left = right := by
    rcases lt_trichotomy left right with hl | heq | hr
    · exact ((retry_data_copy_query_order tiles schedules left right hl a b).ne he).elim
    · exact heq
    · exact ((retry_data_copy_query_order tiles schedules right left hr b a).ne he.symm).elim
  subst right
  refine ⟨rfl,?_⟩
  apply Fin.ext
  cases left <;> simp only [retryDataCopyQuery] at he <;> omega

theorem retry_reply_prepared_query (tiles schedules lane reply tile) :
    (preparedState (replyTileCheckpoint tiles lane reply (schedules lane) tile).1 tile tiles
      (schedules lane tile) (HopperStage.leader lane)).base.scalar.core.queries = retryDataNativeQuery tiles schedules lane tile := by
  rw [preparedState_queries]
  simp only [replyTileCheckpoint,loopCheckpoint_queries]
  rfl

end
end Ptx.Kernels.HopperDoubleBuffer
