import Ptx.Kernels.HopperStageResources
import Ptx.Hopper.TmaObservation

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

theorem each_wait_observes_a : ∀ lane : Wgmma.Lane,
    Tma.observation resourceHistory 2 (4+lane.val) = some (copyId 5,waitId lane) := by decide
theorem each_wait_observes_b : ∀ lane : Wgmma.Lane,
    Tma.observation resourceHistory 3 (4+lane.val) = some (copyId 6,waitId lane) := by decide

end
end Ptx.Kernels.HopperStage
