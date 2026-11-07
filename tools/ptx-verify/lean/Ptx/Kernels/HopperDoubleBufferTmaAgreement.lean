import Ptx.Kernels.HopperDoubleBufferResourceAdmission

/-! Exhaustive actual-copy descriptor and initial-payload agreement. Full
TmaComponents additionally requires combined resource/control acyclicity. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_all_source_copies (a b tiles) (hb : tiles ≤ 2^28) (id : Tma.CopyId) (copy : TmaCopy)
    (he : Tma.copyAt (dataCompleteCandidate a b tiles).view id = some copy) :
    ∃ tile < tiles, (id = dataCopyAId a b tiles tile ∧ copy = dataCopyA a tiles tile) ∨
      (id = dataCopyBId a b tiles tile ∧ copy = dataCopyB b tiles tile) := by
  cases id with
  | mk issue =>
    have hh := Unified.view_tma_iff.mp (Tma.copyAt_iff.mp he)
    have hc := data_candidate_resource_case a b tiles hb issue (.base (.tmaIssue copy)) hh rfl
    cases hc with
    | copyA tile ht => exact ⟨tile,ht,Or.inl ⟨rfl,rfl⟩⟩
    | copyB tile ht => exact ⟨tile,ht,Or.inr ⟨rfl,rfl⟩⟩

theorem data_descriptor_agreement (a b tiles) (hb : tiles ≤ 2^28) :
    Tma.DescriptorAgreement (dataCompleteCandidate a b tiles).view (dataMaps tiles) := by
  intro id copy he
  obtain ⟨tile,ht,hkind⟩ := data_all_source_copies a b tiles hb id copy he
  rcases hkind with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [dataMaps,dataCopyA,dataCopyB]

theorem data_payload_agreement (a b tiles frame) (hb : tiles ≤ 2^28) :
    Tma.PayloadAgreement (dataCompleteCandidate a b tiles).view (dataRepresentedInitial a b tiles frame) := by
  intro id copy he offset ho
  obtain ⟨tile,ht,hkind⟩ := data_all_source_copies a b tiles hb id copy he
  rcases hkind with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact data_copy_a_payload a b tiles tile frame ht ⟨offset,ho⟩
  · exact data_copy_b_payload a b tiles tile frame ht ⟨offset,ho⟩

theorem data_stored_descriptor_agreement (a b tiles frame) (address : Nat) (view : Tma.Descriptor2D)
    (he : dataMaps tiles address = some view) :
    TensorMap.Stored (dataRepresentedInitial a b tiles frame) ⟨.global,address⟩ view := by
  by_cases ha : address = 4096
  · subst address
    have hv : view = aView 65536 tiles := by simpa only [dataMaps,ite_true,Option.some.injEq] using he.symm
    subst view
    exact data_initial_descriptor_a a b tiles frame
  · by_cases hb : address = 4224
    · subst address
      have hv : view = bView (dataBBase tiles) tiles := by simpa only [dataMaps,ha,ite_false,ite_true,Option.some.injEq] using he.symm
      subst view
      exact data_initial_descriptor_b a b tiles frame
    · simp [dataMaps,ha,hb] at he

end
end Ptx.Kernels.HopperDoubleBuffer
