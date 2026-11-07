import Ptx.Kernels.HopperDoubleBufferControlResourceRanks
import Ptx.Hopper.TmaResourceRank

/-! Resource serialization agrees with the same global rank as source and
implicit TMA steps. CTA control and memory visibility are separate checks. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_phase_control_values (a b tiles slot phase) (hp : phase < uses tiles slot) :
    (dataPhaseEntries a b tiles slot phase).map (fun entry => originControlRank tiles entry.origin) =
      List.ofFn (fun i : Fin 131 => phaseRank (stageTile slot phase) i.val) := by
  have ht := (stage_tile_in_range tiles slot phase).mpr hp
  simp only [dataPhaseEntries,List.map_append,List.map_cons,List.map_nil,originControlRank,Tma.Origin.node,controlRank,
    data_expect_control_rank a b tiles _ ht,data_copy_a_control_rank a b tiles _ ht,
    data_copy_b_control_rank a b tiles _ ht,List.map_ofFn,Function.comp_def,data_wait_control_rank a b tiles _ _ ht]
  rw [List.ofFn_add (n := 3) (m := 128)]
  apply congrArg₂ List.append
  · rfl
  · apply congrArg List.ofFn
    funext lane
    simp only [Fin.val_natAdd,phaseRank]
    split_ifs <;> omega

theorem data_phase_control_sorted (a b tiles slot phase) (hp : phase < uses tiles slot) :
    ((dataPhaseEntries a b tiles slot phase).map (fun entry => originControlRank tiles entry.origin)).Pairwise (· < ·) := by
  rw [data_phase_control_values a b tiles slot phase hp]
  apply List.pairwise_ofFn.mpr
  intro left right hlr
  exact phase_rank_strict _ left.val right.val hlr right.isLt

theorem data_phase_control_bounds (a b tiles slot phase) (hp : phase < uses tiles slot) (entry : Tma.Entry)
    (he : entry ∈ dataPhaseEntries a b tiles slot phase) :
    1024*expectSerial (stageTile slot phase) ≤ originControlRank tiles entry.origin ∧
      originControlRank tiles entry.origin ≤ 1024*(8+10*stageTile slot phase)+127 := by
  have hm : originControlRank tiles entry.origin ∈
      (dataPhaseEntries a b tiles slot phase).map (fun entry => originControlRank tiles entry.origin) :=
    List.mem_map.mpr ⟨entry,he,rfl⟩
  rw [data_phase_control_values a b tiles slot phase hp] at hm
  obtain ⟨index,hindex⟩ := List.mem_ofFn.mp hm
  rw [← hindex]
  exact phase_rank_bounds _ index.val index.isLt

theorem data_phases_control_sorted (a b tiles slot n) (hn : n ≤ uses tiles slot) :
    ((dataPhases a b tiles slot n).map (fun entry => originControlRank tiles entry.origin)).Pairwise (· < ·) := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [dataPhases,List.map_append,List.pairwise_append]
    refine ⟨ih (by omega),data_phase_control_sorted a b tiles slot n (by omega),?_⟩
    intro left hl right hr
    obtain ⟨le,hle,rfl⟩ := List.mem_map.mp hl
    obtain ⟨re,hre,rfl⟩ := List.mem_map.mp hr
    obtain ⟨phase,hp,he⟩ := (data_phases_entry a b tiles slot n le).mp hle
    have hleft := data_phase_control_bounds a b tiles slot phase (by omega) le he
    have hright := data_phase_control_bounds a b tiles slot n (by omega) re hre
    have hgap := phase_control_gap (stageTile slot phase) (stageTile slot n) (by dsimp [stageTile]; omega)
    omega

theorem data_history_control_sorted (a b tiles slot) :
    ((dataResourceHistory a b tiles slot).map (fun entry => originControlRank tiles entry.origin)).Pairwise (· < ·) := by
  simp only [dataResourceHistory,List.map_append,List.map_cons,List.map_nil,originControlRank,Tma.Origin.node,controlRank,
    data_init_control_rank,data_inval_control_rank]
  rw [List.pairwise_append,List.pairwise_append]
  refine ⟨⟨by simp,data_phases_control_sorted a b tiles slot _ (Nat.le_refl _),?_⟩,by simp,?_⟩
  · intro left hl right hr
    have he : left = 1024*slot.val := List.mem_singleton.mp hl
    subst left
    obtain ⟨entry,hm,rfl⟩ := List.mem_map.mp hr
    obtain ⟨phase,hp,he⟩ := (data_phases_entry a b tiles slot _ entry).mp hm
    have hb := data_phase_control_bounds a b tiles slot phase hp entry he
    have he := expect_serial_bounds (stageTile slot phase)
    have hs := slot.isLt
    change 1024*slot.val < originControlRank tiles entry.origin
    omega
  · intro left hl right hr
    have he : right = 1024*(10*tiles+14+slot.val) := List.mem_singleton.mp hr
    subst right
    simp only [List.mem_append,List.mem_singleton] at hl
    rcases hl with rfl | hl
    · omega
    · obtain ⟨entry,hm,rfl⟩ := List.mem_map.mp hl
      obtain ⟨phase,hp,he⟩ := (data_phases_entry a b tiles slot _ entry).mp hm
      have hb := data_phase_control_bounds a b tiles slot phase hp entry he
      have ht := (stage_tile_in_range tiles slot phase).mpr hp
      change originControlRank tiles entry.origin < 1024*(10*tiles+14+slot.val)
      omega

theorem data_histories_control_sorted (a b tiles) (loc : Location) :
    ((dataHistories a b tiles loc).map Tma.Entry.origin).Pairwise (fun left right => controlRank tiles left.node < controlRank tiles right.node) := by
  have hzero := data_history_control_sorted a b tiles 0
  have hone := data_history_control_sorted a b tiles 1
  simp only [List.pairwise_map,originControlRank] at hzero hone ⊢
  unfold dataHistories
  split_ifs
  · exact hzero
  · exact hone
  · exact List.Pairwise.nil

theorem control_resource_order (a b tiles) {left right} (he : Tma.ResourceEdge (dataHistories a b tiles) left right) :
    controlRank tiles left < controlRank tiles right :=
  Tma.resource_edge_rank_of_pairwise (data_histories_control_sorted a b tiles) he

end
end Ptx.Kernels.HopperDoubleBuffer
