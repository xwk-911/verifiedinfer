import Ptx.Kernels.HopperStageTmaComponents
import Ptx.Kernels.HopperStageCompletionData
import Ptx.Hopper.ProxyPublication

/-! All actual source waits observe each transfer's own completion, at the
same barrier lifetime/phase. This establishes resource observation only; a
native async WGMMA reader still needs the combined memory/publication rules.
-/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section

def cluster : Access.ClusterScope := fun left right => left.cta = right.cta
theorem stage_a_completion_observed (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Access.CompletionObserved Tma.localShared (candidate a b).view histories cluster (copyId 5) (waitId lane) := by
  refine ⟨rfl,gate,2,4+lane.val,rfl,?_,?_⟩
  · simpa only [histories,ite_true] using stage_history_valid a b
  · simpa only [histories,ite_true] using each_wait_observes_a lane
theorem stage_b_completion_observed (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Access.CompletionObserved Tma.localShared (candidate a b).view histories cluster (copyId 6) (waitId lane) := by
  refine ⟨rfl,gate,3,4+lane.val,rfl,?_,?_⟩
  · simpa only [histories,ite_true] using stage_history_valid a b
  · simpa only [histories,ite_true] using each_wait_observes_b lane

end
end Ptx.Kernels.HopperStage
