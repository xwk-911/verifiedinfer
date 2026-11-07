import Ptx.Kernels.HopperDoubleBufferCopyGeometry
import Ptx.Kernels.HopperDoubleBufferTmaInputs
import Ptx.Hopper.UnifiedImmutable

/-! Descriptor and TMA payload values for arbitrary completed candidates.
Independent initial tensor maps and input bytes, the existing causal memory
conditions and mixed-size-race exclusion determine captured replies. No chosen
data candidate, retry schedule or desired matrix result is assumed. Resource,
native operand publication and arithmetic remain separate obligations. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem candidate_global_input_eligible {tiles sourceInitial candidate histories cluster rf read loc}
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate)
    (hc : Unified.Complete candidate)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor candidate histories cluster rf)
    (hg : loc.space = .global) (hout : ¬(8192 ≤ loc.address ∧ loc.address < 10240)) :
    Unified.Eligible Tma.localShared Access.globalDescriptor candidate histories cluster rf read loc :=
  Unified.immutable_eligible hm (candidate_global_outside_output_immutable hb hw hc hg hout)

theorem candidate_global_input_read {tiles sourceInitial candidate initial histories cluster rf co read loc value}
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate)
    (hc : Unified.Complete candidate)
    (hmem : Unified.CausalConstraints Tma.localShared Access.globalDescriptor candidate initial rf co histories cluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor candidate histories cluster rf)
    (hg : loc.space = .global) (hout : ¬(8192 ≤ loc.address ∧ loc.address < 10240))
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor candidate read loc = some value) :
    rf read loc = none ∧ value = initial read.proxy loc :=
  Unified.immutable_read_source hmem.agreement (candidate_global_input_eligible hb hw hc hm hg hout) hr
    (candidate_global_outside_output_immutable hb hw hc hg hout)

theorem candidate_descriptor_agreement_from_memory {a b tiles frame candidate rf co histories cluster}
    (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate)
    (hc : Unified.Complete candidate)
    (hmem : Unified.CausalConstraints Tma.localShared Access.globalDescriptor candidate
      (fun _ => dataRepresentedInitial a b tiles frame) rf co histories cluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor candidate histories cluster rf) :
    Tma.DescriptorAgreement candidate.view (dataMaps tiles) := by
  intro id copy he
  obtain ⟨tile,_,ha | hb'⟩ := candidate_copy_geometry hb hw hc he
  · have hs : TensorMap.Stored (dataRepresentedInitial a b tiles frame)
        (Access.globalDescriptor id.issue.thread copy.descriptorAddress) (aView 65536 tiles) := by
      rw [ha.1]; exact data_initial_descriptor_a a b tiles frame
    have hi : ∀ writer, Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer
        ((Access.globalDescriptor id.issue.thread copy.descriptorAddress).add 0) = none := by
      rw [ha.1]
      exact candidate_global_outside_output_immutable hb hw hc rfl (by change ¬(8192 ≤ 4096 ∧ 4096 < 10240); decide)
    have hd := Unified.immutable_descriptor_from_memory hmem hm he hs hi
    simp only [dataMaps,ha.1,ite_true,hd]
  · have hs : TensorMap.Stored (dataRepresentedInitial a b tiles frame)
        (Access.globalDescriptor id.issue.thread copy.descriptorAddress) (bView (dataBBase tiles) tiles) := by
      rw [hb'.1]; exact data_initial_descriptor_b a b tiles frame
    have hi : ∀ writer, Unified.writeByte Tma.localShared Access.globalDescriptor candidate writer
        ((Access.globalDescriptor id.issue.thread copy.descriptorAddress).add 0) = none := by
      rw [hb'.1]
      exact candidate_global_outside_output_immutable hb hw hc rfl (by change ¬(8192 ≤ 4224 ∧ 4224 < 10240); decide)
    have hd := Unified.immutable_descriptor_from_memory hmem hm he hs hi
    simp only [dataMaps,hb'.1,show (4224 = 4096) = False from propext (by decide),ite_false,ite_true,hd]

theorem candidate_copy_input_location {tiles sourceInitial candidate id copy offset}
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (he : Tma.copyAt candidate.view id = some copy) (ho : offset < copy.descriptor.bytes) :
    ∃ loc, Tma.sourceByte copy.descriptor copy.coordinates offset = some loc ∧
      loc.space = .global ∧ 65536 ≤ loc.address := by
  have hm := hd id copy he
  obtain ⟨tile,ht,ha | hb'⟩ := candidate_copy_geometry hb hw hc he
  · have hdesc : copy.descriptor = aView 65536 tiles := by
      simpa only [dataMaps,ha.1,ite_true,Option.some.injEq] using hm.symm
    rw [hdesc] at ho ⊢
    rw [ha.2.1]
    exact ⟨⟨.global,65536+2048*tile+offset⟩,a_tile_source ht ho,rfl,by dsimp only; omega⟩
  · have hdesc : copy.descriptor = bView (dataBBase tiles) tiles := by
      simpa only [dataMaps,hb'.1,show (4224 = 4096) = False from propext (by decide),ite_false,ite_true,Option.some.injEq] using hm.symm
    rw [hdesc] at ho ⊢
    rw [hb'.2.1]
    refine ⟨⟨.global,dataBBase tiles+256*tile+offset⟩,b_tile_source ht ho,rfl,?_⟩
    dsimp [dataBBase]; omega

theorem candidate_tma_read_input_bounds {tiles sourceInitial candidate id offset loc}
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hl : Tma.readLocation candidate.view id offset = some loc) : loc.space = .global ∧ 65536 ≤ loc.address := by
  cases he : Tma.copyAt candidate.view id with
  | none => simp only [Tma.readLocation,he,Option.bind_none] at hl; cases hl
  | some copy =>
    have hs : Tma.sourceByte copy.descriptor copy.coordinates offset = some loc := by
      simpa only [Tma.readLocation,he,Option.bind_some] using hl
    obtain ⟨actual,ha,hspace,haddr⟩ := candidate_copy_input_location hb hw hc hd he (Tma.source_byte_some hs).1
    have hx : actual = loc := Option.some.inj (ha.symm.trans hs)
    exact hx ▸ ⟨hspace,haddr⟩

theorem candidate_payload_agreement_from_memory {a b tiles frame candidate rf co histories cluster}
    (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate)
    (hc : Unified.Complete candidate)
    (hmem : Unified.CausalConstraints Tma.localShared Access.globalDescriptor candidate
      (fun _ => dataRepresentedInitial a b tiles frame) rf co histories cluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor candidate histories cluster rf) :
    Tma.PayloadAgreement candidate.view (dataRepresentedInitial a b tiles frame) := by
  have hd := candidate_descriptor_agreement_from_memory hb hw hc hmem hm
  intro id copy he offset ho
  obtain ⟨loc,hs,hg,hbound⟩ := candidate_copy_input_location hb hw hc hd he ho
  have hlen := Unified.tma_copy_payload_length hw he
  have hindex : offset < copy.payload.length := by omega
  have hp : copy.payload[offset]? = some copy.payload[offset] := List.getElem?_eq_getElem hindex
  have hl : Tma.readLocation candidate.view id offset = some loc := by simp only [Tma.readLocation,he,Option.bind_some,hs]
  have hv : Tma.transferByte candidate.view id offset = some copy.payload[offset] := by simp only [Tma.transferByte,he,Option.bind_some,hp]
  have hr := Access.tensor_read (resolve := Tma.localShared) (descriptor := Access.globalDescriptor) hl hv
  have hvalue := (candidate_global_input_read (read := .base (.tma (.read id offset))) hb hw hc hmem hm hg (by omega) hr).2
  simpa only [Tma.byteValue,hs] using hp.trans (congrArg some hvalue)

end
end Ptx.Kernels.HopperDoubleBuffer
