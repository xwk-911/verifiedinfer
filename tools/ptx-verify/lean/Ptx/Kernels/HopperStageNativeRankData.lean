import Ptx.Kernels.HopperStageControlData

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-- Erasure introduces fence placeholders, so only the unambiguous MMA/wait
tags are used to recover native source ranks. -/
def nativeRankTag : Hopper.Event → Option Nat
  | .wgmma .mma => some 310
  | .wgmma .wait => some 330
  | _ => none
theorem native_source_tag_ranks : ∀ id ∈ resourceCandidate.eventIds,
    ∀ expected ∈ ((resourceCandidate.eventAt id).bind nativeRankTag).toList, sourceControlRank id = expected := by decide

end
end Ptx.Kernels.HopperStage
