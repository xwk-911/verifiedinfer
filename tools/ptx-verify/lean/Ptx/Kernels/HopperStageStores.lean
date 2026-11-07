import Ptx.Kernels.HopperStageAddresses

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def storeCount (isLeader : Bool) : Nat := if isLeader then 8 else 7
def storeResult (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    Wgmma.State × List Wgmma.Event :=
  (Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (storeCount isLeader) (at39 a b lane isLeader)).toOption.getD ({},[])
theorem store_succeeds (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    (Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (storeCount isLeader) (at39 a b lane isLeader)).toOption.isSome = true := by
  cases isLeader <;> rfl
theorem store_run (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (storeCount isLeader) (at39 a b lane isLeader) =
      .ok (storeResult a b lane isLeader) := by
  have hh := store_succeeds a b lane isLeader
  cases hr : Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (storeCount isLeader) (at39 a b lane isLeader) with
  | error fault => rw [hr] at hh; cases hh
  | ok value => simp only [storeResult,hr]; rfl
theorem store_complete_metadata (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    (((storeResult a b lane isLeader).1.base.scalar.core.thread.status == .done) &&
      ((Wgmma.pending (storeResult a b lane isLeader).1.ledger).length == 0)) = true := by
  cases isLeader <;> rfl

end
end Ptx.Kernels.HopperStage
