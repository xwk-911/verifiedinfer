import Ptx.Kernels.HopperDoubleBufferCandidateAdmission
import Ptx.Kernels.HopperDoubleBufferMemoryWitness
import Ptx.Tests.HopperCandidateInputs

/-! Mixed-size exclusion for source-complete heterogeneous retries, input
rejections without caller race hypotheses, compatible independent witnesses,
and an actual source-only alias showing why descriptor admission is required.
-/
namespace Ptx.HopperCandidateAdmissionTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev replies := HopperCandidateInputsTests.replies
abbrev schedule := HopperCandidateInputsTests.schedule
def source (payload matrix : ℝ) : Unified.Candidate := HopperCandidateInputsTests.candidate 65536 (dataBBase 1) payload matrix

theorem heterogeneous_copies_are_initial (payload matrix : ℝ) {id copy}
    (he : Tma.copyAt (source payload matrix).view id = some copy) :
    ∃ lane : Wgmma.Lane, copy = replyInitialA (replies 65536 (dataBBase 1) payload matrix lane) ∨
      copy = replyInitialB (replies 65536 (dataBBase 1) payload matrix lane) := by
  have hr := Unified.view_tma_iff.mp (Tma.copyAt_iff.mp he)
  obtain ⟨trace,ht,_,hget⟩ := Unified.eventAt_trace hr
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  have hm := List.mem_of_getElem? hget
  change Wgmma.Event.base (.tmaIssue copy) ∈ replyPositiveEvents 1 lane
    (replies 65536 (dataBBase 1) payload matrix lane) (schedule lane) at hm
  simp only [replyPositiveEvents,List.mem_append] at hm
  rcases hm with (h | h) | h | h
  · exact (initialization_no_tma_issue _ _ h).elim
  · cases hl : HopperStage.leader lane with
    | false => simp [replyInitialCopies,hl] at h
    | true => exact ⟨lane,by simpa [replyInitialCopies,hl] using h⟩
  · simp [loopEvents,iterationEvents,preludeEvents,needsPrefetch,waitEvent,computeEvents,advanceEvents] at h
  · exact (output_no_tma_issue _ _ _ _ _ _ h).elim

theorem heterogeneous_descriptor_admission (payload matrix : ℝ) :
    Tma.DescriptorAgreement (source payload matrix).view (dataMaps 1) := by
  intro id copy he
  obtain ⟨lane,ha | hb⟩ := heterogeneous_copies_are_initial payload matrix he
  · rw [ha]; simp [replyInitialA,replies,HopperCandidateInputsTests.replies,dataMaps]
  · rw [hb]; simp [replyInitialB,replies,HopperCandidateInputsTests.replies,dataMaps]

theorem heterogeneous_no_mixed_size (payload matrix : ℝ) (histories : Location → List Tma.Entry) (cluster : Unified.ClusterScope) (rf : Unified.ReadsFrom) :
    ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (source payload matrix) histories cluster rf :=
  candidate_no_mixed_size_race (by decide)
    (HopperCandidateInputsTests.hostile_replies_source_well_formed 65536 (dataBBase 1) payload matrix (fun _ => .bits (byte 0)))
    (HopperCandidateInputsTests.hostile_replies_source_complete 65536 (dataBBase 1) payload matrix) (heterogeneous_descriptor_admission payload matrix)

theorem wrong_payload_rejected_without_race_premise {payload matrix truth frame rf co histories cluster}
    (hne : payload ≠ truth) :
    ¬Unified.CausalConstraints Tma.localShared Access.globalDescriptor (source payload matrix)
      (fun _ => dataRepresentedInitial (fun _ _ => truth) (fun _ _ => truth) 1 frame) rf co histories cluster :=
  HopperCandidateInputsTests.wrong_payload_cannot_be_admitted hne (heterogeneous_no_mixed_size payload matrix histories cluster rf)

theorem fabricated_rf_rejected_without_race_premise {payload matrix truth frame rf co histories cluster}
    (hc : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (source payload matrix)
      (fun _ => dataRepresentedInitial (fun _ _ => truth) (fun _ _ => truth) 1 frame) rf co histories cluster) (writer : Unified.Node) :
    rf (.base (.tma (.read HopperCandidateInputsTests.copyAId 0))) ⟨.global,65536⟩ ≠ some writer :=
  HopperCandidateInputsTests.fabricated_input_rf_rejected hc (heterogeneous_no_mixed_size payload matrix histories cluster rf) writer

theorem heterogeneous_input_never_written (payload matrix : ℝ) {id offset loc}
    (hl : Tma.readLocation (source payload matrix).view id offset = some loc) (writer : Unified.Node) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (source payload matrix) writer loc = none := by
  have hw := HopperCandidateInputsTests.hostile_replies_source_well_formed 65536 (dataBBase 1) payload matrix (fun _ => .bits (byte 0))
  have hc := HopperCandidateInputsTests.hostile_replies_source_complete 65536 (dataBBase 1) payload matrix
  have hg := candidate_tma_read_input_bounds (by decide) hw hc (heterogeneous_descriptor_admission payload matrix) hl
  exact candidate_global_outside_output_immutable (by decide) hw hc hg.1 (by omega) writer

theorem independent_data_mixed_size_derived (a b tiles) (frame : Location → Symbolic.Byte) (hb : tiles ≤ 2^28) (histories : Location → List Tma.Entry) (cluster : Unified.ClusterScope) (rf : Unified.ReadsFrom) :
    ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) histories cluster rf :=
  candidate_no_mixed_size_race hb (data_source_well_formed a b tiles frame hb) (data_candidate_local a b tiles hb)
    (data_descriptor_agreement a b tiles hb)

theorem independent_components_rebuilt_from_memory (a b tiles frame) (hb : tiles ≤ 2^28) :
    Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame))
      (dataCompleteCandidate a b tiles) Tma.localShared (dataMaps tiles) (dataHistories a b tiles) :=
  candidate_components_from_memory hb (data_source_well_formed a b tiles _ hb) (data_candidate_local a b tiles hb)
    (data_descriptor_agreement a b tiles hb) (data_memory_witness a b tiles frame hb).toCausalConstraints
    (data_all_histories_valid a b tiles hb) (data_control_acyclic a b tiles)

theorem components_imply_mixed_size_exclusion (a b tiles) (frame : Location → Symbolic.Byte) (hb : tiles ≤ 2^28) (cluster : Unified.ClusterScope) (rf : Unified.ReadsFrom) :
    ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) (dataHistories a b tiles) cluster rf :=
  candidate_components_no_mixed_size hb (independent_components_rebuilt_from_memory a b tiles frame hb)

theorem zero_tile_mixed_size_derived (a b) (frame : Location → Symbolic.Byte) (histories : Location → List Tma.Entry) (cluster : Unified.ClusterScope) (rf : Unified.ReadsFrom) :
    ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 0) histories cluster rf :=
  independent_data_mixed_size_derived a b 0 frame (by decide) histories cluster rf

def aliasSource (payload matrix : ℝ) : Unified.Candidate := HopperCandidateInputsTests.candidate 8192 (dataBBase 1) payload matrix
def aliasRead : Unified.Node := .base (.tma (.read HopperCandidateInputsTests.copyAId 0))
def aliasWrite : Unified.Node := .base (.tma (.source ⟨(ctx 1 0).id,15⟩))

theorem alias_source_is_complete (payload matrix : ℝ) (initial : Location → Symbolic.Byte) :
    Unified.WellFormed code (completeLaunch 1 initial) (aliasSource payload matrix) ∧ Unified.Complete (aliasSource payload matrix) :=
  ⟨HopperCandidateInputsTests.hostile_replies_source_well_formed 8192 (dataBBase 1) payload matrix initial,
    HopperCandidateInputsTests.hostile_replies_source_complete 8192 (dataBBase 1) payload matrix⟩

theorem alias_actual_read_footprint (payload matrix : ℝ) :
    (Unified.kind Tma.localShared Access.globalDescriptor (aliasSource payload matrix) aliasRead).bind Ptx.Event.Kind.footprint =
      some (⟨.global,8192⟩,1) := by
  have hl : Tma.readLocation (aliasSource payload matrix).view HopperCandidateInputsTests.copyAId 0 = some ⟨.global,8192⟩ := by
    simp only [aliasSource,Tma.readLocation,HopperCandidateInputsTests.actual_initial_a,Option.bind_some]
    exact a_tile_source (tile := 0) (by decide) (by decide)
  have hv : Tma.transferByte (aliasSource payload matrix).view HopperCandidateInputsTests.copyAId 0 = some (.realPart .f16 payload 0) := by
    simp only [aliasSource,Tma.transferByte,HopperCandidateInputsTests.actual_initial_a,Option.bind_some]; rfl
  simp [Unified.kind,aliasRead,Access.kind,hl,hv,Ptx.Event.Kind.footprint]

theorem alias_actual_write_footprint (payload matrix : ℝ) :
    (Unified.kind Tma.localShared Access.globalDescriptor (aliasSource payload matrix) aliasWrite).bind Ptx.Event.Kind.footprint =
      some (⟨.global,8192⟩,4) := by
  have he : (aliasSource payload matrix).eventAt ⟨(ctx 1 0).id,15⟩ =
      some (outputWriteEvent 0 (fun _ => matrix) 0) := by
    change (replyCandidate 1 (replies 8192 (dataBBase 1) payload matrix) schedule).eventAt
      ⟨(replyTrace 1 (replies 8192 (dataBBase 1) payload matrix) schedule 0).id,15⟩ = _
    rw [Unified.eventAt_of_member (reply_source_ids_unique 1 (replies 8192 (dataBBase 1) payload matrix) schedule)
      (List.mem_ofFn.mpr ⟨(0 : Wgmma.Lane),rfl⟩)]
    rfl
  simp only [Unified.kind,aliasWrite,Access.kind,Unified.view_eventAt,he,Option.map_some,Unified.eventView,
    outputWriteEvent,Option.bind_some,Ptx.Event.Kind.footprint,Symbolic.encode_length]
  rfl

theorem source_only_mixed_footprints_can_overlap (payload matrix : ℝ) :
    ¬Unified.SameFootprint Tma.localShared Access.globalDescriptor (aliasSource payload matrix) aliasRead aliasWrite := by
  rintro ⟨fp,hr,hw⟩
  have hread := (alias_actual_read_footprint payload matrix).symm.trans hr
  have hwrite := (alias_actual_write_footprint payload matrix).symm.trans hw
  have he := Option.some.inj (hread.trans hwrite.symm)
  have hs := congrArg Prod.snd he
  norm_num at hs

theorem alias_descriptor_admission_rejected (payload matrix : ℝ) :
    ¬Tma.DescriptorAgreement (aliasSource payload matrix).view (dataMaps 1) := by
  intro hd
  have hh := hd _ _ (HopperCandidateInputsTests.actual_initial_a 8192 (dataBBase 1) payload matrix)
  have he : aView 65536 1 = aView 8192 1 := by
    simpa only [replyInitialA,HopperCandidateInputsTests.replies,dataMaps,ite_true,Option.some.injEq] using hh
  have hb := congrArg TensorMap.Descriptor2D.base he
  norm_num [aView] at hb

end
end Ptx.HopperCandidateAdmissionTests
