import Ptx.Kernels.HopperStageObservedOutput
import Ptx.Tests.UnifiedMemory
import Ptx.Tests.HopperStageAdmission

/-! Parameterized memory/observer nonvacuity, concrete nonuniform matrix
corners, frame guards, and semantic rejection of omitted/stale observations.
The values are symbolic real fragments, not IEEE hardware execution bytes. -/
namespace Ptx.HopperStageMemoryWitnessTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperStage
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev a := WgmmaTensorTests.nonuniformA
abbrev b := WgmmaTensorTests.nonuniformB
abbrev frame := HopperStageAdmissionTests.frame
theorem arbitrary_memory_exists (left : Wgmma.ACoord → ℝ) (right : Wgmma.BCoord → ℝ) (padding : Location → Symbolic.Byte) :
    ∃ rf co, Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate left right)
      (initialProxyMemory left right padding) rf co histories cluster ∧
      ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate left right) histories cluster rf :=
  stage_memory_exists left right padding
theorem concrete_memory_component : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b)
    (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster := stage_memory_witness a b frame
theorem concrete_observer_component : Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b)
    (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster (observation a b frame) := stage_observer_witness a b frame
theorem nonuniform_first_output : (observation a b frame).output ⟨.global,8192⟩ = .realPart .f32 1 0 := by
  have hh := independent_observed_matrix a b frame 0 0 0
  have ha : ((⟨.global,wordAddress 0 0⟩ : Location).add 0) = ⟨.global,8192⟩ := by decide
  change (observation a b frame).output ((⟨.global,wordAddress 0 0⟩ : Location).add 0) = _ at hh
  rw [ha] at hh
  norm_num [a,b,Wgmma.matrixStep,Wgmma.cCoord,WgmmaTensorTests.nonuniformA,WgmmaTensorTests.nonuniformB,Fin.sum_univ_succ] at hh
  exact hh
theorem nonuniform_last_output : (observation a b frame).output ⟨.global,10239⟩ = .realPart .f32 1472 3 := by
  have hh := independent_observed_matrix a b frame 127 3 3
  have ha : ((⟨.global,wordAddress 127 3⟩ : Location).add 3) = ⟨.global,10239⟩ := by decide
  change (observation a b frame).output ((⟨.global,wordAddress 127 3⟩ : Location).add 3) = _ at hh
  rw [ha] at hh
  norm_num [a,b,Wgmma.matrixStep,Wgmma.cCoord,WgmmaTensorTests.nonuniformA,WgmmaTensorTests.nonuniformB,Fin.sum_univ_succ] at hh
  exact hh
theorem lower_guard_preserved : (observation a b frame).output ⟨.global,8191⟩ = .bits (byte 165) :=
  independent_observed_frame a b frame _ (mem_output_domain.mpr (by decide)) (by decide)
theorem upper_guard_preserved : (observation a b frame).output ⟨.global,10240⟩ = .bits (byte 165) :=
  independent_observed_frame a b frame _ (mem_output_domain.mpr (by decide)) (by decide)
theorem omitted_observer_rejected : ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b)
    (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster (omittedObservation a b frame) :=
  omitted_output_rejected a b frame
theorem stale_observer_rejected : ¬Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b)
    (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster (staleObservation a b frame) :=
  stale_output_rejected a b frame
theorem output_owner_corners : outputOwner 8192 = (0,0) ∧ outputOwner 10239 = (127,3) := by decide
theorem memory_rank_separates_producer_native_wait :
    memoryRank (nativeProducer UnifiedMemoryTests.firstA) < memoryRank (nativeRead UnifiedMemoryTests.firstA) ∧
    memoryRank (nativeRead UnifiedMemoryTests.firstA) < memoryRank (.base (.tma (.source (nativeWaitId 127)))) := by decide

end
end Ptx.HopperStageMemoryWitnessTests
