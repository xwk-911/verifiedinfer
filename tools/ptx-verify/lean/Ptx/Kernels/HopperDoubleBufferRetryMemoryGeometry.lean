import Ptx.Kernels.HopperDoubleBufferRetryNativeReuse
import Ptx.Kernels.HopperDoubleBufferMemoryGeometry
import Ptx.Kernels.HopperDoubleBufferCandidateAdmission

/-! All actual writers of a native read byte in arbitrary completed retry
candidates. Physical regions identify A/B, slot and offset; no unique writer
across tiles, RF choice or captured operand value agreement is assumed. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_all_source_copies {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (id : Tma.CopyId) (copy : TmaCopy)
    (he : Tma.copyAt candidate.view id = some copy) :
    ∃ tile < tiles,
      (id = family.copyAId tile ∧ copy = replyCopyA tiles (family.replies 0) (family.schedules 0) tile) ∨
      (id = family.copyBId tile ∧ copy = replyCopyB tiles (family.replies 0) (family.schedules 0) tile) := by
  cases id with
  | mk issue =>
    have hh := Unified.view_tma_iff.mp (Tma.copyAt_iff.mp he)
    have hc := retry_candidate_resource_case family ht hw issue (.base (.tmaIssue copy)) hh rfl
    cases hc with
    | copyA tile hp => exact ⟨tile,hp,Or.inl ⟨rfl,rfl⟩⟩
    | copyB tile hp => exact ⟨tile,hp,Or.inr ⟨rfl,rfl⟩⟩

theorem retry_tensor_write_region {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) {id offset loc}
    (hl : Tma.writeLocation Tma.localShared candidate.view id offset = some loc) :
    ∃ tile < tiles,
      (id = family.copyAId tile ∧ offset < 2048 ∧ loc = ⟨.shared .zero,aBase (stage tile)+offset⟩) ∨
      (id = family.copyBId tile ∧ offset < 256 ∧ loc = ⟨.shared .zero,bBase (stage tile)+offset⟩) := by
  cases hc : Tma.copyAt candidate.view id with
  | none => simp only [Tma.writeLocation,hc,Option.bind_none] at hl; cases hl
  | some copy =>
    obtain ⟨tile,hp,hcopy⟩ := retry_all_source_copies family ht hw id copy hc
    refine ⟨tile,hp,?_⟩
    rcases hcopy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have hx := hl
      rw [Tma.writeLocation,family_copy_a_at family hw tile hp] at hx
      simp only [Option.bind_some,family_copy_a_descriptor family hw hd tile hp] at hx
      have ho : offset < 2048 := by
        change (if offset < 2048 then _ else none) = some loc at hx
        split at hx
        · assumption
        · cases hx
      have he := retry_transfer_a_location family hw hd tile hp ⟨offset,ho⟩
      exact Or.inl ⟨rfl,ho,Option.some.inj (hl.symm.trans he)⟩
    · have hx := hl
      rw [Tma.writeLocation,family_copy_b_at family hw tile hp] at hx
      simp only [Option.bind_some,family_copy_b_descriptor family hw hd tile hp] at hx
      have ho : offset < 256 := by
        change (if offset < 256 then _ else none) = some loc at hx
        split at hx
        · assumption
        · cases hx
      have he := retry_transfer_b_location family hw hd tile hp ⟨offset,ho⟩
      exact Or.inr ⟨rfl,ho,Option.some.inj (hl.symm.trans he)⟩

theorem retry_native_a_location {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (p : Wgmma.ACoord) (part : Fin 2) :
    retryNativeLocation family tile (.a p part) = ⟨.shared .zero,aBase (stage tile)+(Wgmma.aOffset (p,part)).val⟩ :=
  reply_operand_a_location tiles 0 (family.replies 0) (family.schedules 0) tile p part
theorem retry_native_b_location {tiles candidate} (family : ReplySourceFamily tiles candidate) (tile : Nat) (p : Wgmma.BCoord) (part : Fin 2) :
    retryNativeLocation family tile (.b p part) = ⟨.shared .zero,bBase (stage tile)+(Wgmma.bOffset (p,part)).val⟩ :=
  reply_operand_b_location tiles 0 (family.replies 0) (family.schedules 0) tile p part

theorem retry_native_writer_case {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28) {tile operand writer value}
    (he : Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer (retryNativeLocation family tile operand) = some value) :
    ∃ source < tiles, stage source = stage tile ∧ writer = retryNativeProducer family source operand := by
  have hs : (retryNativeLocation family tile operand).space = .shared .zero := by cases operand <;> rfl
  obtain ⟨id,offset,rfl,hl⟩ := candidate_shared_writer_is_tensor hb hw hc hs he
  obtain ⟨source,hp,hregion⟩ := retry_tensor_write_region family ht hw hd hl
  refine ⟨source,hp,?_⟩
  cases operand with
  | a p part =>
    rw [retry_native_a_location] at hregion
    rcases hregion with ⟨rfl,ho,he⟩ | ⟨rfl,ho,he⟩
    · have hx := a_region_unique (stage tile) (stage source) (Wgmma.aOffset (p,part)).val offset (Wgmma.aOffset (p,part)).isLt ho (congrArg Location.address he)
      rw [← hx.2]
      exact ⟨hx.1.symm,rfl⟩
    · exact (a_b_regions_disjoint (stage tile) (stage source) _ _ (Wgmma.aOffset (p,part)).isLt ho (congrArg Location.address he)).elim
  | b p part =>
    rw [retry_native_b_location] at hregion
    rcases hregion with ⟨rfl,ho,he⟩ | ⟨rfl,ho,he⟩
    · exact (a_b_regions_disjoint (stage source) (stage tile) _ _ ho (Wgmma.bOffset (p,part)).isLt (congrArg Location.address he).symm).elim
    · have hx := b_region_unique (stage tile) (stage source) (Wgmma.bOffset (p,part)).val offset (Wgmma.bOffset (p,part)).isLt ho (congrArg Location.address he)
      rw [← hx.2]
      exact ⟨hx.1.symm,rfl⟩

end
end Ptx.Kernels.HopperDoubleBuffer
