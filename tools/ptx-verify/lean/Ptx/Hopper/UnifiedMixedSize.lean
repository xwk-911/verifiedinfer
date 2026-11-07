import Ptx.Hopper.UnifiedOrder
import Ptx.Hopper.UnifiedFootprints

/-! Mixed-size exclusion derived from actual conflicting access footprints.
The premise covers every unified writer/access, not just TMA or native nodes.
This rule does not assert general race freedom, value agreement or memory
existence. -/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

theorem compatible_conflicts_no_mixed_size_race {resolve descriptor c histories cluster rf}
    (h : ∀ writer other loc value, writeByte resolve descriptor c writer loc = some value →
      Accesses resolve descriptor c other loc → SameFootprint resolve descriptor c writer other) :
    ¬MixedSizeRace resolve descriptor c histories cluster rf := by
  rintro ⟨loc,left,right,hrace,hsize⟩
  rcases hrace.conflict with hw | hw
  · obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp hw
    exact hsize (h left right loc value hv hrace.right)
  · obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp hw
    obtain ⟨footprint,hr,hl⟩ := h right left loc value hv hrace.left
    exact hsize ⟨footprint,hl,hr⟩

end
end Ptx.Hopper.Unified
