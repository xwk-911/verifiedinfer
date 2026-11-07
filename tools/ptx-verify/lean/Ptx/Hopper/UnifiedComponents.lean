import Ptx.Hopper.UnifiedStep
import Ptx.Hopper.InputValues

/-! Compose source-checked unified executions with existing TMA/resource
components on their number-preserving view. This does not assert legacy source
admission, full combined WGMMA memory/RF, collective tensor or runtime legality.
No weaker payload shape is assumed: it follows from actual delegated TMA steps.
-/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

structure TmaComponents (code : List Instr) (launch : Scalar.Launch) (candidate : Candidate)
    (resolve : Tma.SharedResolver) (maps : Nat → Option Tma.Descriptor2D)
    (histories : Location → List Tma.Entry) : Prop where
  source : WellFormed code launch candidate
  complete : Complete candidate
  descriptors : Tma.DescriptorAgreement candidate.view maps
  payload : Tma.PayloadAgreement candidate.view launch.initial
  histories_valid : ∀ loc, Tma.HistoryValid resolve candidate.view loc (histories loc)
  control : Tma.ControlAcyclic candidate.view histories

theorem tensor_byte_present {candidate : Candidate} {resolve descriptor code launch id op offset}
    (hw : WellFormed code launch candidate) (hc : Tma.copyAt candidate.view id = some op) (ho : offset < op.descriptor.bytes) :
    ∃ value, Tma.transferByte candidate.view id offset = some value ∧
      Access.kind resolve descriptor candidate.view (.tma (.write id offset)) =
        some (.write ((resolve id.issue.thread op.destination).add offset) [value]) :=
  Access.tensor_byte_present_of_length (tma_copy_payload_length hw hc) hc ho
theorem payload_agreement_from_memory {candidate : Candidate} {resolve descriptor initial eligible rf code launch}
    (hw : WellFormed code launch candidate)
    (ha : Access.ReadAgreement resolve descriptor candidate.view initial eligible rf)
    (hz : Access.ZeroFill candidate.view)
    (he : ∀ id offset loc, Tma.readLocation candidate.view id offset = some loc → eligible (.tma (.read id offset)) loc)
    (hi : ∀ id offset loc, Tma.readLocation candidate.view id offset = some loc → Access.Immutable resolve descriptor candidate.view loc) :
    Tma.PayloadAgreement candidate.view (initial .async) :=
  Access.payload_agreement_from_memory_of_length (fun _ _ hc => tma_copy_payload_length hw hc) ha hz he hi
theorem notification_matches_payload {candidate : Candidate} {resolve code launch id event}
    (hw : WellFormed code launch candidate) (he : Tma.notification resolve candidate.view id = some event) :
    ∃ copy, Tma.copyAt candidate.view id = some copy ∧ event.operation = .completeTx copy.payload.length := by
  obtain ⟨copy,hcopy,_,hop⟩ := Tma.notification_has_actual_copy he
  exact ⟨copy,hcopy,by simpa only [tma_copy_payload_length hw hcopy] using hop⟩
theorem tag_has_no_barrier {candidate : Candidate} {id tag}
    (he : candidate.view.eventAt id = some (.wgmma tag)) : candidate.view.barrierAt id = none := by
  simp only [Hopper.Candidate.barrierAt,he,Option.bind_some]
theorem tag_has_no_cta_rendezvous {candidate : Candidate} {id tag}
    (he : candidate.view.eventAt id = some (.wgmma tag)) (arrival : Bool) : candidate.view.ctaTag arrival id = none := by
  simp only [Hopper.Candidate.ctaTag,he,Option.bind_some]
theorem tag_has_no_ordinary_access {candidate : Candidate} {resolve descriptor id tag}
    (he : candidate.view.eventAt id = some (.wgmma tag)) :
    Access.kind resolve descriptor candidate.view (.tma (.source id)) = none := by
  simp only [Access.kind,he,Option.bind_some]

end
end Ptx.Hopper.Unified
