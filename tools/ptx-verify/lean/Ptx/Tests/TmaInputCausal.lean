import Ptx.Hopper.ByteWitness
import Ptx.Hopper.AccessInversion
import Ptx.Tests.TmaInputValues

/-! Independent causal-component witness for the actual padded TMA helper.
All of its real reads are covered, including the complete descriptor and every
in-bounds data byte. The helper has no generic shared consumer. This does not
replace the independent full consumer/GEMM admission and observer obligations. -/
namespace Ptx.TmaInputCausalTests
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 500000

theorem read_in_input_sites {node loc value}
    (hr : Access.readByte Tma.localShared Access.globalDescriptor TmaTests.candidate node loc = some value) :
    TmaInputTests.InputSites node loc := by
  have ha : Access.Accesses Tma.localShared Access.globalDescriptor TmaTests.candidate node loc := .inl (by rw [hr]; rfl)
  cases node with
  | copyRead issue | copyWrite issue => simp [Access.readByte,Access.kind,TmaInputTests.no_nonbulk] at hr
  | tma node =>
    cases node with
    | source event => simp [Access.readByte,TmaInputTests.no_ordinary] at hr
    | descriptor actual =>
      cases hc : Tma.copyAt TmaTests.candidate actual with
      | none => simp [Access.readByte,Access.kind,hc] at hr
      | some op =>
        obtain ⟨rfl,rfl⟩ := TmaInputTests.only_copy hc
        have hb := Access.access_bounds ha (show (Access.kind Tma.localShared Access.globalDescriptor TmaTests.candidate _).bind
          Ptx.Event.Kind.footprint = some (⟨.global,4096⟩,128) by simp [Access.kind,hc,Access.globalDescriptor,Ptx.Event.Kind.footprint,TensorMap.encode_length]; rfl)
        have ho : loc.address-4096 < 128 := by simp only at hb; omega
        refine .inl ⟨loc.address-4096,ho,rfl,?_⟩
        rcases loc with ⟨space,address⟩
        simp only at hb
        simp only [Location.add,Location.mk.injEq]
        exact ⟨hb.1.symm,by omega⟩
    | read actual offset =>
      have hl := Access.tensor_read_access ha
      obtain ⟨op,hc,_⟩ := Tma.read_has_copy (by rw [hl]; rfl)
      obtain ⟨rfl,_⟩ := TmaInputTests.only_copy hc
      exact .inr ⟨offset,hl,rfl⟩
    | write actual offset =>
      obtain ⟨k,hk⟩ := Access.access_kind ha
      obtain ⟨location,byte,_,_,rfl⟩ := Access.tensor_write_shape hk
      simp [Access.readByte,hk,Ptx.Event.Kind.readByte] at hr
    | notify actual => cases hr

theorem every_read_global {node loc value}
    (hr : Access.readByte Tma.localShared Access.globalDescriptor TmaTests.candidate node loc = some value) : loc.space = .global := by
  rcases read_in_input_sites hr with ⟨_,_,_,rfl⟩ | ⟨offset,hl,_⟩
  · rfl
  · have hs : Tma.sourceByte TmaTests.view TmaTests.coords offset = some loc := by
      simpa [Tma.readLocation,TmaTests.copy_from_actual_issue,TmaTests.copy] using hl
    exact (Tma.source_byte_some hs).2.2.1

theorem every_read_agrees {node loc value}
    (hr : Access.readByte Tma.localShared Access.globalDescriptor TmaTests.candidate node loc = some value) :
    Access.sourceValue Tma.localShared Access.globalDescriptor TmaTests.candidate TmaInputTests.initial node loc
      (TmaInputTests.rf node loc) = some value :=
  TmaInputTests.agreement node loc value (read_in_input_sites hr) hr

def cluster : Access.ClusterScope := fun a b => a.cta = b.cta

def co := Access.RankedCo Tma.localShared Access.globalDescriptor TmaTests.candidate (fun _ => 0)

theorem causal_witness : Access.CausalConstraints Tma.localShared Access.globalDescriptor TmaTests.candidate
    TmaInputTests.initial TmaInputTests.rf co TmaTests.histories cluster := by
  refine ⟨fun _ _ _ _ hr => every_read_agrees hr,?_,?_,?_⟩
  · intro _ writer loc value hw
    exact ⟨trivial,by rw [Access.sourcePresent,Access.WritesAt,hw]; rfl,by simp [Access.sourceRank]⟩
  · intro _ writer read loc vw vr hw hr _
    have hspace := every_read_global hr
    cases loc with
    | mk space address =>
      cases hspace
      rw [TmaInputTests.global_immutable address writer] at hw
      cases hw
  · intro _ read writer loc vr vw hr hw _
    have hspace := every_read_global hr
    cases loc with
    | mk space address =>
      cases hspace
      rw [TmaInputTests.global_immutable address writer] at hw
      cases hw

theorem actual_complete_causal_witness :
    WellFormed Generated.hopper_tma_copy.program TmaTests.launch TmaTests.candidate ∧ Complete TmaTests.candidate ∧
    Access.CausalConstraints Tma.localShared Access.globalDescriptor TmaTests.candidate TmaInputTests.initial TmaInputTests.rf co
      TmaTests.histories cluster := ⟨TmaTests.formed,TmaTests.complete,causal_witness⟩

end
end Ptx.TmaInputCausalTests
