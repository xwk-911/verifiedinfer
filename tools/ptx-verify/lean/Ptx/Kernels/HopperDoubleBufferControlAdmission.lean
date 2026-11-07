import Ptx.Kernels.HopperDoubleBufferControlCtaRanks
import Ptx.Hopper.UnifiedComponents

/-! All four TMA control edge classes share one increasing rank. This closes
the source/resource/control/input TMA components of the repeated witness, not
combined memory, native-control, ISA eligibility or final observer admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section

theorem data_control_acyclic (a b tiles) :
    Tma.ControlAcyclic (dataCompleteCandidate a b tiles).view (dataHistories a b tiles) :=
  Tma.control_acyclic_of_rank (controlRank tiles)
    (fun _ _ => control_program_order a b tiles)
    (fun _ _ => control_cta_order a b tiles)
    (fun _ _ => control_internal_order a b tiles)
    (fun _ _ => control_resource_order a b tiles)

theorem data_tma_components (a b tiles frame) (hb : tiles ≤ 2^28) :
    Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial a b tiles frame))
      (dataCompleteCandidate a b tiles) Tma.localShared (dataMaps tiles) (dataHistories a b tiles) :=
  ⟨data_source_well_formed a b tiles _ hb,data_candidate_local a b tiles hb,
    data_descriptor_agreement a b tiles hb,data_payload_agreement a b tiles frame hb,
    data_all_histories_valid a b tiles hb,data_control_acyclic a b tiles⟩

end
end Ptx.Kernels.HopperDoubleBuffer
