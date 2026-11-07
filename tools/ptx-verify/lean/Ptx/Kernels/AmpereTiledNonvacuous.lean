import Ptx.Kernels.AmpereTiledWitnessComponents
import Ptx.Kernels.AmpereTiledWitnessInactive
import Ptx.Kernels.AmpereTiledBarrierSources

/-! Complete legal executions for the unchanged tiled-matmul precondition.
The witnesses are constructed independently of the universal correctness proof;
zero K and inactive output guards require no additional input assumptions. -/
namespace Ptx.AmpereTiledNonvacuous
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph
noncomputable section

theorem active_checked {cfg launch a b} (hp : Pre cfg a b launch) (ha : Active cfg) :
    CheckedConditions code launch (AmpereTiledWitnessOracle.execution cfg launch a b)
      AmpereTiledWitnessMemory.rf (AmpereTiledWitnessMemory.co cfg launch a b) := by
  have hs := AmpereTiledWitnessOracle.source hp ha
  exact ⟨hs.formed,AmpereTiledBarrierSources.aligned hs,AmpereTiledControl.barriers hs,
    AmpereTiledControl.control hs,AmpereTiledWitnessMemory.memory hp ha,AmpereTiledWitnessMma.mma hp ha⟩

theorem nonvacuous (cfg : Config) (a b : Matrix) :
    CheckedNonvacuous code (Pre cfg a b) (fun _ => domain cfg) := by
  intro launch hp
  by_cases ha : Active cfg
  · exact ⟨AmpereTiledWitnessOracle.execution cfg launch a b,AmpereTiledWitnessMemory.rf,
      AmpereTiledWitnessMemory.co cfg launch a b,AmpereTiledWitnessObservation.observation cfg launch a b,
      active_checked hp ha,AmpereTiledWitnessObservation.observer hp ha,rfl⟩
  · exact ⟨AmpereTiledWitnessInactive.execution cfg launch,AmpereTiledWitnessInactive.rf,
      AmpereTiledWitnessInactive.co cfg launch,AmpereTiledWitnessInactive.observation cfg launch,
      AmpereTiledWitnessInactive.checked hp ha,AmpereTiledWitnessInactive.observer cfg launch,rfl⟩

end
end Ptx.AmpereTiledNonvacuous
