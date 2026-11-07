import Ptx.Hopper.UnifiedControlCheck
import Ptx.Kernels.HopperStageNativeControl
import Ptx.Kernels.HopperStageObservedOutput
import Ptx.Tests.HopperStageMemoryWitness
import Ptx.Tests.HopperCollectiveCycleBase

/-! Actual positive native-control/independent-memory composition, warp-local
rendezvous and all-lane source-PC linkage. No blanket memory visibility follows
from these control assertions. Cycle evidence uses a generated source fixture.
-/
namespace Ptx.HopperNativeControlTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperStage
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem arbitrary_stage_control (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Unified.ControlAdmitted block (candidate a b) histories := stage_native_control_admitted a b
theorem actual_all_warp_source_pcs (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (who : Wgmma.Lane) (index : Fin 4) (lane : Fin 32) :
    ∃ other, Unified.NativeSync block (candidate a b) other (nativeId who index) ∧
      (candidate a b).sourcePC Generated.hopper_gemm_stage.program params block other = some (nativeSignature index).pc :=
  Unified.synced_participants_source_pc (source_well_formed a b (fun _ => .bits (byte 0)))
    (stage_schedules_admitted a b) (actual_native_signature a b who index) lane
theorem independent_control_memory_observer (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) :
    Unified.ControlAdmitted block (candidate a b) histories ∧
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (candidate a b)
      (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster ∧
    Unified.ObserverConditions Tma.localShared Access.globalDescriptor (candidate a b)
      (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster (observation a b frame) :=
  ⟨stage_native_control_admitted a b,stage_memory_witness a b frame,stage_observer_witness a b frame⟩
theorem same_warp_fence_matches : Unified.NativeSync block (candidate UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB)
    (nativeId 0 0) (nativeId 31 0) := by decide
theorem next_warp_fence_does_not_sync : ¬Unified.NativeSync block (candidate UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB)
    (nativeId 0 0) (nativeId 32 0) := by decide
theorem same_warp_different_instruction_does_not_sync : ¬Unified.NativeSync block (candidate UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB)
    (nativeId 0 0) (nativeId 31 1) := by decide
theorem leader_and_peer_fence_serials_differ : (nativeId 0 0).serial = 8 ∧ (nativeId 31 0).serial = 3 := by decide
theorem control_rank_places_arrival_before_return :
    nativeControlRank (.arrival (nativeId 0 0)) < nativeControlRank (.base (.source (nativeId 31 0))) := by decide
theorem source_returns_are_not_rendezvous_arrivals :
    ¬Unified.NativeArrival (candidate UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB)
      (.base (.source (nativeId 0 0))) (.arrival (nativeId 0 0)) := Unified.native_self_return_cannot_arrive
theorem native_peer_returns_unordered (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (left right : Wgmma.Lane) (index : Fin 4) :
    ¬Ptx.Event.Path (Unified.ControlEdge block (candidate a b) histories)
      (.base (.source (nativeId left index))) (.base (.source (nativeId right index))) := by
  intro ho
  have hh := ho.rank_lt nativeControlRank (fun _ _ => native_control_edge_rank)
  change 2*sourceControlRank (nativeId left index) < 2*sourceControlRank (nativeId right index) at hh
  rw [native_id_rank,native_id_rank] at hh
  omega
theorem legacy_control_passes_new_control_rejects :
    Tma.ControlAcyclic HopperCollectiveCycleTests.candidate.view (fun _ => []) ∧
    Unified.SchedulesAdmitted block HopperCollectiveCycleTests.candidate ∧
    ¬Unified.ControlAdmitted block HopperCollectiveCycleTests.candidate (fun _ => []) :=
  ⟨HopperCollectiveCycleTests.old_control_acyclic,HopperCollectiveCycleTests.schedules_match,
    HopperCollectiveCycleTests.every_resource_family_rejected _⟩
theorem complete_aligned_source_still_has_cycle (family : Location → List Tma.Entry) :
    Unified.WellFormed Generated.hopper_collective_cycle.program HopperCollectiveCycleTests.launch HopperCollectiveCycleTests.candidate ∧
    Unified.Complete HopperCollectiveCycleTests.candidate ∧
    Unified.SchedulesAdmitted block HopperCollectiveCycleTests.candidate ∧
    ¬Unified.ControlAdmitted block HopperCollectiveCycleTests.candidate family :=
  ⟨HopperCollectiveCycleTests.source_well_formed,HopperCollectiveCycleTests.source_complete,
    HopperCollectiveCycleTests.schedules_match,HopperCollectiveCycleTests.every_resource_family_rejected family⟩

end
end Ptx.HopperNativeControlTests
