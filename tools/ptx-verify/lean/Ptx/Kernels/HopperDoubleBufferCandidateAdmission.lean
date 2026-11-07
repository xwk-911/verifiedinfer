import Ptx.Kernels.HopperDoubleBufferCandidateRegions

/-! Input-memory closure for arbitrary completed candidates using the existing
descriptor admission. Mixed-size exclusion is derived, not a caller premise.
Resource histories/control remain checked fields; collective/native memory,
allocation/lifetime, observer and full-Pre refinement are not inferred. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section

theorem candidate_input_read_from_descriptors {tiles sourceInitial candidate initial histories cluster rf co read loc value}
    (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hmem : Unified.CausalConstraints Tma.localShared Access.globalDescriptor candidate initial rf co histories cluster)
    (hg : loc.space = .global) (hout : ¬(8192 ≤ loc.address ∧ loc.address < 10240))
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor candidate read loc = some value) :
    rf read loc = none ∧ value = initial read.proxy loc :=
  candidate_global_input_read hb hw hc hmem (candidate_no_mixed_size_race hb hw hc hd) hg hout hr

theorem candidate_payload_from_descriptors {a b tiles frame candidate rf co histories cluster}
    (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hmem : Unified.CausalConstraints Tma.localShared Access.globalDescriptor candidate
      (fun _ => dataRepresentedInitial a b tiles frame) rf co histories cluster) :
    Tma.PayloadAgreement candidate.view (dataRepresentedInitial a b tiles frame) :=
  candidate_payload_agreement_from_memory hb hw hc hmem (candidate_no_mixed_size_race hb hw hc hd)

theorem candidate_components_from_memory {a b tiles frame candidate rf co histories cluster}
    (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles (dataRepresentedInitial a b tiles frame)) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hmem : Unified.CausalConstraints Tma.localShared Access.globalDescriptor candidate
      (fun _ => dataRepresentedInitial a b tiles frame) rf co histories cluster)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hcontrol : Tma.ControlAcyclic candidate.view histories) :
    Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame))
      candidate Tma.localShared (dataMaps tiles) histories :=
  ⟨hw,hc,hd,candidate_payload_from_descriptors hb hw hc hd hmem,hh,hcontrol⟩

theorem candidate_components_no_mixed_size {tiles initial candidate histories cluster rf} (hb : tiles ≤ 2^28)
    (h : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) histories) :
    ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor candidate histories cluster rf :=
  candidate_no_mixed_size_race hb h.source h.complete h.descriptors

end
end Ptx.Kernels.HopperDoubleBuffer
