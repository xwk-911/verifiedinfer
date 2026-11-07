import Ptx.Kernels.AmpereTiledWitnessObservation
import Ptx.Kernels.AmpereTiledWitnessMma

/-! Independent complete active source/rf/co/observer components. This intermediate
assembly is extended by AmpereTiledNonvacuous with actual dynamic barrier-source
matching and the inactive branch to establish the full checked witness. -/
namespace Ptx.AmpereTiledWitnessComponents
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph
noncomputable section

theorem components {cfg launch a b} (hp : Pre cfg a b launch) (ha : Active cfg) :
    ∃ candidate rf co o, WellFormed code launch candidate ∧ Complete candidate ∧
      BarrierParticipation candidate ∧ ControlAcyclic candidate ∧ MmaConditions code launch candidate ∧
      MemoryConstraints candidate launch.initial rf co ∧ ObserverConstraints candidate launch.initial rf co o ∧
      o.domain = domain cfg := by
  have hs := AmpereTiledWitnessOracle.source hp ha
  exact ⟨AmpereTiledWitnessOracle.execution cfg launch a b,AmpereTiledWitnessMemory.rf,
    AmpereTiledWitnessMemory.co cfg launch a b,AmpereTiledWitnessObservation.observation cfg launch a b,
    hs.formed,hs.complete,AmpereTiledControl.barriers hs,AmpereTiledControl.control hs,
    AmpereTiledWitnessMma.mma hp ha,AmpereTiledWitnessMemory.memory hp ha,
    AmpereTiledWitnessObservation.observer hp ha,rfl⟩

end
end Ptx.AmpereTiledWitnessComponents
