import Ptx.Kernels.HopperStageStoreInventory

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem tensor_written_operand {a b id offset loc}
    (hl : Tma.writeLocation Tma.localShared (candidate a b).view id offset = some loc) :
    ∃ operand, nativeLocation a b operand = loc := by
  rcases tensor_write_id_cases hl with rfl | rfl
  · simp only [Tma.writeLocation,actual_copy_a,Option.bind_some] at hl
    split at hl
    · rename_i ho
      change offset < 2048 at ho
      let owner := Wgmma.aByteOwner ⟨offset,ho⟩
      refine ⟨.a owner.1 owner.2,?_⟩
      rw [nativeLocation,a_operand_location]
      have he := Wgmma.a_offset_owner ⟨offset,ho⟩
      change Wgmma.aOffset owner = _ at he
      rw [he]
      exact Option.some.inj hl
    · cases hl
  · simp only [Tma.writeLocation,actual_copy_b,Option.bind_some] at hl
    split at hl
    · rename_i ho
      change offset < 256 at ho
      let owner := Wgmma.bByteOwner ⟨offset,ho⟩
      refine ⟨.b owner.1 owner.2,?_⟩
      rw [nativeLocation,b_operand_location]
      have he := Wgmma.b_offset_owner ⟨offset,ho⟩
      change Wgmma.bOffset owner = _ at he
      rw [he]
      exact Option.some.inj hl
    · cases hl
theorem global_writer_is_source {a b writer loc value} (hg : loc.space = .global)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) writer loc = some value) :
    ∃ event, writer = .base (.tma (.source event)) := by
  cases writer with
  | wgmmaRead issue operand => rw [Unified.native_write_none] at hw; cases hw
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.writeByte,Unified.kind,Access.kind,no_nonbulk] at hw
    | tma node =>
      cases node with
      | source event => exact ⟨event,rfl⟩
      | descriptor id => rw [Unified.base_write_preserved,Access.descriptor_no_write] at hw; cases hw
      | read id offset => rw [Unified.base_write_preserved,Access.tensor_read_no_write] at hw; cases hw
      | notify id => cases hw
      | write id offset =>
        have hl := Access.tensor_write_access (.inr (by rw [← Unified.base_write_preserved,hw]; rfl))
        have hs := tensor_write_shared_space hl
        have he := hs.symm.trans hg
        cases he
theorem global_writer_metadata {a b writer loc value} (hg : loc.space = .global)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) writer loc = some value) :
    ∃ lane slot, writer = .base (.tma (.source (storeId lane slot))) ∧
      wordAddress lane slot ≤ loc.address ∧ loc.address < wordAddress lane slot+4 := by
  obtain ⟨event,rfl⟩ := global_writer_is_source hg hw
  obtain ⟨base,size,hf⟩ := Unified.access_footprint_exists (.inr (by rw [hw]; rfl))
  obtain ⟨lane,slot,rfl,rfl,rfl⟩ := source_indexed_footprint_shape hf
  have hb := Unified.access_footprint_bounds (.inr (by rw [hw]; rfl)) hf
  exact ⟨lane,slot,rfl,hb.2⟩
theorem overlapping_output_words {left right : Wgmma.Lane} {first last : Wgmma.Slot} {address : Nat}
    (hl : wordAddress left first ≤ address ∧ address < wordAddress left first+4)
    (hr : wordAddress right last ≤ address ∧ address < wordAddress right last+4) :
    (left,first) = (right,last) := by
  have he : wordAddress left first = wordAddress right last := by
    have ha := (word_address_bounds left first).2.2
    have hb := (word_address_bounds right last).2.2
    omega
  rw [wordAddress,wordAddress,actual_output_address,actual_output_address] at he
  apply Wgmma.c_unique_owner
  have hcol := (Wgmma.cCoord (left,first)).2.isLt
  have hother := (Wgmma.cCoord (right,last)).2.isLt
  apply Prod.ext <;> apply Fin.ext <;> omega
theorem stage_unique_writers {a b loc left right vl vr}
    (hl : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) left loc = some vl)
    (hr : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) right loc = some vr) : left = right := by
  obtain ⟨base,size,hf,hs | ho⟩ := write_footprint_regions hl
  all_goals have hb := Unified.access_footprint_bounds (.inr (by rw [hl]; rfl)) hf
  · have hshared : loc.space = .shared .zero := hb.1.symm.trans hs.1
    obtain ⟨id,offset,rfl,hw⟩ := shared_writer_is_tensor hshared hl
    obtain ⟨operand,hoperand⟩ := tensor_written_operand hw
    rw [← hoperand] at hl hr
    exact (native_producer_unique hl).trans (native_producer_unique hr).symm
  · have hg : loc.space = .global := hb.1.symm.trans ho.1
    obtain ⟨leftLane,leftSlot,rfl,hleft⟩ := global_writer_metadata hg hl
    obtain ⟨rightLane,rightSlot,rfl,hright⟩ := global_writer_metadata hg hr
    have he := overlapping_output_words hleft hright
    cases he
    rfl
theorem stage_coherence (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (rf : Unified.ReadsFrom) :
    Unified.Coherent Tma.localShared Access.globalDescriptor (candidate a b) histories cluster rf (coherenceWitness a b) := by
  apply Unified.unique_initial_coherent (fun _ _ _ _ _ => stage_unique_writers)
  intro loc writer value _ hc
  have hh := memory_causality_rank hc
  omega

end
end Ptx.Kernels.HopperStage
