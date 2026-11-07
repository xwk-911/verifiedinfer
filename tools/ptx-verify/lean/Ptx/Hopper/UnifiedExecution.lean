import Ptx.Hopper.UnifiedComponents
import Ptx.Hopper.UnifiedControl
import Ptx.Hopper.UnifiedMemory
import Ptx.Hopper.UnifiedObservation
import Ptx.Hopper.UnifiedCollective

/-! One explicit package of the existing model components. Tensor admission
ranges over actual source-matched collectives. This does not add allocation,
ownership, physical ISA, compiler or runtime assumptions to the event model,
and must not be read as a hardware execution or termination theorem. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

structure TensorComponents (candidate : Candidate) : Prop where
  covered : ∀ event mark call, candidate.eventAt event = some (.mma mark call) →
    ∃ issue, ∃ collective : Collective candidate issue, ∃ lane, collective.sources lane = event
  tensor : ∀ issue, ∀ collective : Collective candidate issue,
    ∃ memory, Wgmma.TensorConditions issue.thread.cta collective.calls memory

structure ExecutionComponents (code : List Instr) (launch : Scalar.Launch) (candidate : Candidate)
    (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (maps : Nat → Option Tma.Descriptor2D)
    (initial : ProxyMemory) (rf : ReadsFrom) (co : Location → Option Node → Option Node → Prop)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (observation : Observation) : Prop where
  tma : TmaComponents code launch candidate resolve maps histories
  control : ControlAdmitted launch.geometry.block candidate histories
  memory : MemoryConditions resolve descriptor candidate initial rf co histories cluster
  tensor : TensorComponents candidate
  observer : ObserverConditions resolve descriptor candidate initial rf co histories cluster observation

theorem tensor_components_of_no_mma {candidate : Candidate}
    (hn : ∀ event mark call, candidate.eventAt event ≠ some (.mma mark call)) : TensorComponents candidate := by
  constructor
  · intro event mark call he
    exact (hn event mark call he).elim
  · intro issue collective
    exact (hn (collective.sources 0) (collective.marks 0) (collective.calls 0) (collective.matched 0)).elim

theorem execution_components_iff {code launch candidate resolve descriptor maps initial rf co histories cluster observation} :
    ExecutionComponents code launch candidate resolve descriptor maps initial rf co histories cluster observation ↔
      TmaComponents code launch candidate resolve maps histories ∧
      ControlAdmitted launch.geometry.block candidate histories ∧
      MemoryConditions resolve descriptor candidate initial rf co histories cluster ∧
      TensorComponents candidate ∧ ObserverConditions resolve descriptor candidate initial rf co histories cluster observation := by
  constructor
  · intro h
    exact ⟨h.tma,h.control,h.memory,h.tensor,h.observer⟩
  · rintro ⟨tma,control,memory,tensor,observer⟩
    exact ⟨tma,control,memory,tensor,observer⟩

theorem execution_source_complete {code launch candidate resolve descriptor maps initial rf co histories cluster observation}
    (he : ExecutionComponents code launch candidate resolve descriptor maps initial rf co histories cluster observation) :
    WellFormed code launch candidate ∧ Complete candidate := ⟨he.tma.source,he.tma.complete⟩

end
end Ptx.Hopper.Unified
