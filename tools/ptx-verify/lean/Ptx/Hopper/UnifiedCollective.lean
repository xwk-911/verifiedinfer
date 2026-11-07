import Ptx.Hopper.UnifiedAccess
import Ptx.Hopper.WgmmaTensor

/-! Checkable links from all 128 lanes of one collective to actual rich source
events. These records alone do not establish matching fence/commit/wait
schedules, full ISA control, weak memory or resource/lifetime admission. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

structure Collective (candidate : Candidate) (issue : Ptx.Event.EventId) where
  calls : Wgmma.Lane → Wgmma.Call
  marks : Wgmma.Lane → Wgmma.Mark
  sources : Wgmma.Lane → Ptx.Event.EventId
  representative : sources 0 = issue
  matched : ∀ lane, candidate.eventAt (sources lane) = some (.mma (marks lane) (calls lane))
  sameCTA : ∀ lane, (sources lane).thread.cta = issue.thread.cta
  sameMark : ∀ lane, marks lane = marks 0
  cohort : Wgmma.Cohort calls

theorem collective_representative {candidate issue} (collective : Collective candidate issue) :
    candidate.representativeAt issue = some (collective.marks 0,collective.calls 0) := by
  apply representative_at_of_event
  · simpa only [collective.representative] using collective.matched 0
  · rw [collective.cohort.lane]
    rfl
theorem collective_member_ids_unique {candidate issue} (collective : Collective candidate issue) :
    Function.Injective collective.sources := by
  intro left right he
  have hl := collective.matched left
  have hr := collective.matched right
  rw [he] at hl
  have hh := Option.some.inj (hl.symm.trans hr)
  have hc : collective.calls left = collective.calls right := (Wgmma.Event.mma.inj hh).2
  have hh := congrArg Wgmma.Call.lane hc
  simpa only [collective.cohort.lane] using hh
theorem collective_all_lanes_present {candidate issue} (collective : Collective candidate issue) (lane : Wgmma.Lane) :
    ∃ event mark call, candidate.eventAt event = some (.mma mark call) ∧ call.lane = lane :=
  ⟨collective.sources lane,collective.marks lane,collective.calls lane,collective.matched lane,collective.cohort.lane lane⟩
theorem collective_missing_lane_rejected {candidate issue} (lane : Wgmma.Lane)
    (hm : ∀ event mark call, candidate.eventAt event = some (.mma mark call) → call.lane ≠ lane) :
    IsEmpty (Collective candidate issue) := by
  constructor
  intro collective
  exact hm _ _ _ (collective.matched lane) (collective.cohort.lane lane)
theorem collective_members_have_source {candidate issue code launch}
    (hw : WellFormed code launch candidate) (collective : Collective candidate issue) (lane : Wgmma.Lane) :
    ∃ located, candidate.sourceAt code launch.params launch.geometry.block (collective.sources lane) = some located ∧
      located.kind = .mma (collective.marks lane) (collective.calls lane) ∧
      ∃ oracle before after emitted,
        Wgmma.step {id := (collective.sources lane).thread,params := launch.params,block := launch.geometry.block} oracle code before = .ok (after,emitted) ∧
        Wgmma.Event.mma (collective.marks lane) (collective.calls lane) ∈ emitted ∧ located.pc = before.base.scalar.core.thread.pc :=
  source_event hw (collective.matched lane)
theorem collective_tensor_payload_uniform {candidate issue memory}
    (collective : Collective candidate issue)
    (ht : Wgmma.TensorConditions issue.thread.cta collective.calls memory) (lane : Wgmma.Lane) (operand : Wgmma.OperandByte) :
    (collective.calls lane).operandBytes operand.index = (collective.calls 0).operandBytes operand.index := by
  obtain ⟨a,b,hv,_⟩ := ht.tensor
  cases operand with
  | a p byte => exact ((hv lane).1 p byte).trans ((hv 0).1 p byte).symm
  | b p byte => exact ((hv lane).2 p byte).trans ((hv 0).2 p byte).symm
theorem collective_tensor_correct {candidate issue memory a b c}
    (collective : Collective candidate issue)
    (ht : Wgmma.TensorConditions issue.thread.cta collective.calls memory)
    (hm : Wgmma.MatrixStorage issue.thread.cta (collective.calls 0) memory a b)
    (hc : ∀ p, (collective.calls p.1).input p.2 = Wgmma.gatherC c p) :
    Wgmma.scatterC (fun p => (collective.calls p.1).output p.2) = Wgmma.matrixStep a b c :=
  Wgmma.tensor_correct_accumulator ht hm hc

end
end Ptx.Hopper.Unified
