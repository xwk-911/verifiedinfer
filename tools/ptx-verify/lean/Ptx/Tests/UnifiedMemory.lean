import Ptx.Kernels.HopperStageNativeEligibility
import Ptx.Kernels.HopperStageNativePrefix
import Ptx.Tests.Unified

/-! Native byte-memory rules and actual source prefixes. Causal memory
existence and the full kernel observer are still separate obligations. No
synthetic source/global-memory conformance is asserted by the metadata tests.
-/
namespace Ptx.UnifiedMemoryTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def firstA : Wgmma.OperandByte := .a (0,0) 0
def lastB : Wgmma.OperandByte := .b (15,7) 1
def zerosA : Wgmma.ACoord → ℝ := fun _ => 0
def zerosB : Wgmma.BCoord → ℝ := fun _ => 0
def initialRf : Unified.ReadsFrom := fun _ _ => none
theorem initial_rf_rejected (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (initial : Unified.ProxyMemory)
    (co : Location → Option Unified.Node → Option Unified.Node → Prop) :
    ¬Unified.CausalConstraints Tma.localShared Access.globalDescriptor (HopperStage.candidate a b) initial initialRf co HopperStage.histories HopperStage.cluster := by
  intro hc
  have hh := HopperStage.native_rf_forced hc firstA
  cases hh
theorem first_byte_published (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (HopperStage.candidate a b) HopperStage.histories HopperStage.cluster
      (HopperStage.nativeLocation a b firstA) (HopperStage.nativeProducer firstA) (HopperStage.nativeRead firstA) :=
  HopperStage.actual_native_byte_order a b firstA
theorem last_byte_published (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (HopperStage.candidate a b) HopperStage.histories HopperStage.cluster
      (HopperStage.nativeLocation a b lastB) (HopperStage.nativeProducer lastB) (HopperStage.nativeRead lastB) :=
  HopperStage.actual_native_byte_order a b lastB
theorem native_byte_eligibility (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (rf : Unified.ReadsFrom) :
    Unified.Eligible Tma.localShared Access.globalDescriptor (HopperStage.candidate a b) HopperStage.histories HopperStage.cluster rf
      (HopperStage.nativeRead lastB) (HopperStage.nativeLocation a b lastB) := HopperStage.native_eligibility_derived a b rf lastB
theorem complete_wait_acknowledges (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Unified.WgmmaCompletedAt (HopperStage.candidate a b) (HopperStage.mmaId 0) (HopperStage.nativeWaitId 127) :=
  HopperStage.actual_native_completed a b 127
theorem actual_prefix_has_all_lanes (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    ∀ lane, ∃ id mark call, (HopperStage.prefixCandidate a b).eventAt id = some (.mma mark call) ∧ call.lane = lane :=
  fun lane => Unified.collective_all_lanes_present (HopperStage.prefix_collective a b) lane
theorem actual_prefix_no_reuse (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (target : Unified.Node) :
    ¬Unified.NativeReuse Tma.localShared (HopperStage.prefixCandidate a b) (HopperStage.nativeLocation a b firstA)
      (HopperStage.nativeRead firstA) target := HopperStage.prefix_cannot_justify_reuse a b _ _ _ _ target
theorem ordinary_source_order_does_not_publish {c : Unified.Candidate} {source issue operand loc}
    (hn : ∀ fence cta, c.view.eventAt fence ≠ some (.proxyFenceAsyncShared cta)) :
    ¬Unified.GenericReady c source issue operand loc := Unified.no_proxy_fence_no_generic_ready hn
theorem first_and_last_locations :
    HopperStage.nativeLocation zerosA zerosB firstA = ⟨.shared .zero,16⟩ ∧
    HopperStage.nativeLocation zerosA zerosB lastB = ⟨.shared .zero,2319⟩ := by decide
theorem first_and_last_producers :
    HopperStage.nativeProducer firstA = .base (.tma (.write (HopperStage.copyId 5) 0)) ∧
    HopperStage.nativeProducer lastB = .base (.tma (.write (HopperStage.copyId 6) 255)) := by decide
theorem native_footprint_one :
    (Unified.kind Tma.localShared Access.globalDescriptor (HopperStage.candidate zerosA zerosB)
      (HopperStage.nativeRead firstA)).bind Ptx.Event.Kind.footprint = some (⟨.shared .zero,16⟩,1) := by decide
theorem prefix_metadata :
    (HopperStage.prefixTrace zerosA zerosB 0).count = 31 ∧
    (HopperStage.prefixTrace zerosA zerosB 127).count = 26 ∧
    (HopperStage.prefixTrace zerosA zerosB 127).final.ledger.completed = 0 ∧
    (HopperStage.prefixTrace zerosA zerosB 127).final.ledger.groups = 1 := by decide

end
end Ptx.UnifiedMemoryTests
