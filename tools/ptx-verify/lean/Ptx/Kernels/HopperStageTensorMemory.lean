import Ptx.Kernels.HopperStageObservedOutput
import Ptx.Hopper.UnifiedTensorMemory

/-! The same representative memory-to-tensor bridge for the one-stage source.
This proves reuse of the rule, not a second asynchronous ownership method.
-/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section

theorem stage_tensor_from_memory {a b initial rf co}
    (hc : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate a b) initial rf co histories cluster) :
    Wgmma.TensorConditions .zero (calls a b) (transferView a b) :=
  Unified.collective_tensor_from_memory (collective a b) hc nativeProducer (native_eligibility_derived a b rf)
    (native_rf_forced hc) (native_producer_write a b) shifted_a_profile shifted_b_profile
    (transfer_storage a b (calls a b 0) rfl rfl) (tensor_component a b).tensor

theorem stage_tensor_result_from_memory {a b initial rf co}
    (hc : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate a b) initial rf co histories cluster) :
    Wgmma.scatterC (fun p => (calls a b p.1).output p.2) = Wgmma.matrixStep a b (fun _ => 0) := by
  apply Unified.collective_arithmetic_result_from_memory (collective a b) hc nativeProducer (native_eligibility_derived a b rf)
    (native_rf_forced hc) (native_producer_write a b) (transfer_storage a b (calls a b 0) rfl rfl) (tensor_component a b).tensor
  intro p
  change accumulatorInput p.2 = 0
  rw [accumulator_zero]

end
end Ptx.Kernels.HopperStage
