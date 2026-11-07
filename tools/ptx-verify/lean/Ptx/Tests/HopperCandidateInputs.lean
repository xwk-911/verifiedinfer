import Ptx.Kernels.HopperDoubleBufferCandidateInputs
import Ptx.Kernels.HopperDoubleBufferMemoryWitness
import Ptx.Tests.HopperCandidateMemory
import Ptx.Tests.HopperKernelReconstruction

/-! Source-complete hostile descriptor/payload replies with heterogeneous
retries, their rejection by actual input memory, and nonvacuous integration
with the independent arbitrary-data memory witness. No real-value decider. -/
namespace Ptx.HopperCandidateInputsTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev schedule := HopperCandidateMemoryTests.schedule
def replies (baseA baseB : Nat) (payload matrix : ℝ) (lane : Wgmma.Lane) : Wgmma.Oracle :=
  {HopperCandidateMemoryTests.replies matrix lane with
    base := {(HopperCandidateMemoryTests.replies matrix lane).base with
      descriptor := fun q => if q = 0 then aView baseA 1 else bView baseB 1
      tmaBytes := fun q => if q = 1 then HopperStage.aPayload (fun _ => payload) else HopperStage.bPayload (fun _ => payload)}}
def candidate (baseA baseB : Nat) (payload matrix : ℝ) : Unified.Candidate :=
  replyCandidate 1 (replies baseA baseB payload matrix) schedule
def copyAId : Tma.CopyId := ⟨⟨(ctx 1 0).id,6⟩⟩
def copyBId : Tma.CopyId := ⟨⟨(ctx 1 0).id,7⟩⟩

theorem hostile_replies_source_well_formed (baseA baseB payload matrix initial) :
    Unified.WellFormed code (completeLaunch 1 initial) (candidate baseA baseB payload matrix) := by
  apply reply_candidate_well_formed 1 (replies baseA baseB payload matrix) schedule initial (by decide) (by decide)
  · intro lane _
    exact ⟨HopperStage.a_payload_length (fun _ => payload),HopperStage.b_payload_length (fun _ => payload)⟩
  · intro lane i hi
    have he : i = 0 := by omega
    subst i
    refine ⟨?_,?_,?_⟩
    · intro j hj
      change decide (HopperCandidateMemoryTests.firstQuery lane+schedule lane 0 ≤ HopperCandidateMemoryTests.firstQuery lane+j) = false
      simp only [decide_eq_false_iff_not]; omega
    · change decide (HopperCandidateMemoryTests.firstQuery lane+schedule lane 0 ≤ HopperCandidateMemoryTests.firstQuery lane+schedule lane 0) = true
      simp only [decide_eq_true_eq]; exact Nat.le_refl _
    · intro hn; have hh := hn.1; omega

theorem hostile_replies_source_complete (baseA baseB payload matrix) :
    Unified.Complete (candidate baseA baseB payload matrix) :=
  reply_candidate_complete 1 (replies baseA baseB payload matrix) schedule (by decide) (by decide)

theorem actual_initial_a (baseA baseB payload matrix) :
    Tma.copyAt (candidate baseA baseB payload matrix).view copyAId =
      some (replyInitialA (replies baseA baseB payload matrix 0)) := by
  apply Tma.copyAt_iff.mpr
  apply Unified.view_tma_iff.mpr
  change (replyCandidate 1 (replies baseA baseB payload matrix) schedule).eventAt
    ⟨(replyTrace 1 (replies baseA baseB payload matrix) schedule 0).id,6⟩ = _
  rw [Unified.eventAt_of_member (reply_source_ids_unique 1 (replies baseA baseB payload matrix) schedule)
    (List.mem_ofFn.mpr ⟨(0 : Wgmma.Lane),rfl⟩)]
  rfl

theorem actual_initial_b (baseA baseB payload matrix) :
    Tma.copyAt (candidate baseA baseB payload matrix).view copyBId =
      some (replyInitialB (replies baseA baseB payload matrix 0)) := by
  apply Tma.copyAt_iff.mpr
  apply Unified.view_tma_iff.mpr
  change (replyCandidate 1 (replies baseA baseB payload matrix) schedule).eventAt
    ⟨(replyTrace 1 (replies baseA baseB payload matrix) schedule 0).id,7⟩ = _
  rw [Unified.eventAt_of_member (reply_source_ids_unique 1 (replies baseA baseB payload matrix) schedule)
    (List.mem_ofFn.mpr ⟨(0 : Wgmma.Lane),rfl⟩)]
  rfl

theorem hostile_actual_copy_geometry (baseA baseB payload matrix) {id copy}
    (he : Tma.copyAt (candidate baseA baseB payload matrix).view id = some copy) : CopyGeometry 1 copy :=
  candidate_copy_geometry (by decide) (hostile_replies_source_well_formed baseA baseB payload matrix (fun _ => .bits (byte 0)))
    (hostile_replies_source_complete baseA baseB payload matrix) he

theorem admitted_a_base_forced {baseA baseB payload matrix truth frame rf co histories cluster}
    (hmem : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate baseA baseB payload matrix)
      (fun _ => dataRepresentedInitial (fun _ _ => truth) (fun _ _ => truth) 1 frame) rf co histories cluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate baseA baseB payload matrix) histories cluster rf) :
    baseA = 65536 := by
  have hd := candidate_descriptor_agreement_from_memory (by decide)
    (hostile_replies_source_well_formed baseA baseB payload matrix _) (hostile_replies_source_complete baseA baseB payload matrix) hmem hm
      copyAId _ (actual_initial_a baseA baseB payload matrix)
  have he : aView 65536 1 = aView baseA 1 := by simpa only [replyInitialA,replies,dataMaps,ite_true,Option.some.injEq] using hd
  exact (congrArg TensorMap.Descriptor2D.base he).symm

theorem admitted_b_base_forced {baseA baseB payload matrix truth frame rf co histories cluster}
    (hmem : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate baseA baseB payload matrix)
      (fun _ => dataRepresentedInitial (fun _ _ => truth) (fun _ _ => truth) 1 frame) rf co histories cluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate baseA baseB payload matrix) histories cluster rf) :
    baseB = dataBBase 1 := by
  have hd := candidate_descriptor_agreement_from_memory (by decide)
    (hostile_replies_source_well_formed baseA baseB payload matrix _) (hostile_replies_source_complete baseA baseB payload matrix) hmem hm
      copyBId _ (actual_initial_b baseA baseB payload matrix)
  have he : bView (dataBBase 1) 1 = bView baseB 1 := by
    simpa only [replyInitialB,replies,dataMaps,show (4224 = 4096) = False from propext (by decide),
      show (2 = 0) = False from propext (by decide),ite_false,ite_true,Option.some.injEq] using hd
  exact (congrArg TensorMap.Descriptor2D.base he).symm

theorem wrong_descriptor_cannot_be_admitted {baseA baseB payload matrix truth frame rf co histories cluster}
    (hne : baseA ≠ 65536 ∨ baseB ≠ dataBBase 1)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate baseA baseB payload matrix) histories cluster rf) :
    ¬Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate baseA baseB payload matrix)
      (fun _ => dataRepresentedInitial (fun _ _ => truth) (fun _ _ => truth) 1 frame) rf co histories cluster := by
  intro hc
  exact hne.elim (fun h => h (admitted_a_base_forced hc hm)) (fun h => h (admitted_b_base_forced hc hm))

theorem admitted_payload_forced {payload matrix truth frame rf co histories cluster}
    (hmem : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate 65536 (dataBBase 1) payload matrix)
      (fun _ => dataRepresentedInitial (fun _ _ => truth) (fun _ _ => truth) 1 frame) rf co histories cluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate 65536 (dataBBase 1) payload matrix) histories cluster rf) :
    payload = truth := by
  have hp := candidate_payload_agreement_from_memory (by decide)
    (hostile_replies_source_well_formed 65536 (dataBBase 1) payload matrix _) (hostile_replies_source_complete 65536 (dataBBase 1) payload matrix) hmem hm
      copyAId _ (actual_initial_a 65536 (dataBBase 1) payload matrix) 0 (by change 0 < 2048; decide)
  change (HopperStage.aPayload (fun _ => payload))[0]? = some (Tma.byteValue (aView 65536 1) ⟨0,0⟩
    (dataRepresentedInitial (fun _ _ => truth) (fun _ _ => truth) 1 frame) 0) at hp
  have hs : Tma.sourceByte (aView 65536 1) ⟨0,0⟩ 0 = some ⟨.global,65536⟩ := by
    exact a_tile_source (tile := 0) (by decide) (by decide)
  rw [Tma.copied_byte hs] at hp
  have hinit := data_initial_a_byte (fun _ _ => truth) (fun _ _ => truth) 1 0 frame (by decide) ⟨0,by decide⟩
  change dataRepresentedInitial (fun _ _ => truth) (fun _ _ => truth) 1 frame ⟨.global,65536⟩ =
    Wgmma.tileByte (fun _ => truth) (fun _ => truth) 0 at hinit
  rw [hinit] at hp
  have hv : Symbolic.Byte.realPart .f16 payload 0 = .realPart .f16 truth 0 := Option.some.inj hp
  exact (Symbolic.Byte.realPart.inj hv).2.1

theorem wrong_payload_cannot_be_admitted {payload matrix truth frame rf co histories cluster}
    (hne : payload ≠ truth)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate 65536 (dataBBase 1) payload matrix) histories cluster rf) :
    ¬Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate 65536 (dataBBase 1) payload matrix)
      (fun _ => dataRepresentedInitial (fun _ _ => truth) (fun _ _ => truth) 1 frame) rf co histories cluster := by
  intro hc; exact hne (admitted_payload_forced hc hm)

theorem actual_first_input_read (payload matrix : ℝ) :
    Unified.readByte Tma.localShared Access.globalDescriptor (candidate 65536 (dataBBase 1) payload matrix)
      (.base (.tma (.read copyAId 0))) ⟨.global,65536⟩ = some (.realPart .f16 payload 0) := by
  have hl : Tma.readLocation (candidate 65536 (dataBBase 1) payload matrix).view copyAId 0 = some ⟨.global,65536⟩ := by
    simp only [Tma.readLocation,actual_initial_a,Option.bind_some]
    exact a_tile_source (tile := 0) (by decide) (by decide)
  have hv : Tma.transferByte (candidate 65536 (dataBBase 1) payload matrix).view copyAId 0 = some (.realPart .f16 payload 0) := by
    simp only [Tma.transferByte,actual_initial_a,Option.bind_some]
    rfl
  exact Access.tensor_read (resolve := Tma.localShared) (descriptor := Access.globalDescriptor) hl hv

theorem fabricated_input_rf_rejected {payload matrix truth frame rf co histories cluster}
    (hmem : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate 65536 (dataBBase 1) payload matrix)
      (fun _ => dataRepresentedInitial (fun _ _ => truth) (fun _ _ => truth) 1 frame) rf co histories cluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate 65536 (dataBBase 1) payload matrix) histories cluster rf)
    (writer : Unified.Node) : rf (.base (.tma (.read copyAId 0))) ⟨.global,65536⟩ ≠ some writer := by
  have hs := (candidate_global_input_read (by decide)
    (hostile_replies_source_well_formed 65536 (dataBBase 1) payload matrix
      (dataRepresentedInitial (fun _ _ => truth) (fun _ _ => truth) 1 frame))
    (hostile_replies_source_complete 65536 (dataBBase 1) payload matrix) hmem hm rfl
    (by change ¬(8192 ≤ 65536 ∧ 65536 < 10240); decide) (actual_first_input_read payload matrix)).1
  rw [hs]; intro h; cases h

theorem independent_data_witness_inputs (a b tiles frame) (hb : tiles ≤ 2^28) :
    Tma.DescriptorAgreement (dataCompleteCandidate a b tiles).view (dataMaps tiles) ∧
      Tma.PayloadAgreement (dataCompleteCandidate a b tiles).view (dataRepresentedInitial a b tiles frame) := by
  have hw := data_source_well_formed a b tiles (dataRepresentedInitial a b tiles frame) hb
  have hc := data_candidate_local a b tiles hb
  have hmem := (data_memory_witness a b tiles frame hb).toCausalConstraints
  have hm := data_no_mixed_size_race a b tiles hb (dataReadWitness a b tiles)
  exact ⟨candidate_descriptor_agreement_from_memory hb hw hc hmem hm,candidate_payload_agreement_from_memory hb hw hc hmem hm⟩

theorem retrying_full_producer_copy_geometry {copy}
    (he : Wgmma.Event.base (.tmaIssue copy) ∈ HopperKernelReconstructionTests.fullEvents) : CopyGeometry 2 copy := by
  obtain ⟨retries,_,_,_,_,hevents⟩ := completed_positive_source_reconstruct (by decide) (by decide)
    HopperKernelReconstructionTests.full_producer_source HopperIterationReconstructionTests.producer_source_done
  rw [hevents] at he
  exact positive_copy_geometry (by decide) (by decide) he

theorem zero_tile_actual_copy_rejected (a b) (frame : Location → Symbolic.Byte) {id copy} :
    Tma.copyAt (dataCompleteCandidate a b 0).view id ≠ some copy := by
  intro he
  obtain ⟨tile,ht,_⟩ := candidate_copy_geometry (by decide)
    (data_source_well_formed a b 0 frame (by decide)) (data_candidate_local a b 0 (by decide)) he
  omega

end
end Ptx.HopperCandidateInputsTests
