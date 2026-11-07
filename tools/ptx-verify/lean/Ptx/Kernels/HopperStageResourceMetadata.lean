import Ptx.Kernels.HopperStageResources

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

theorem resource_copies : Tma.copies resourceCandidate = [copyId 5,copyId 6] := by decide
theorem resource_locations : ∀ origin ∈ Tma.origins resourceCandidate,
    (Tma.resourceAt Tma.localShared resourceCandidate origin).map BarrierEvent.location = some gate := by decide

end
end Ptx.Kernels.HopperStage
