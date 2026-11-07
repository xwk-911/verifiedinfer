import Ptx.Kernels.HopperStageStores

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def tailCount (isLeader : Bool) : Nat := if isLeader then 18 else 17
def tailResult (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    Wgmma.State × List Wgmma.Event :=
  ((storeResult a b lane isLeader).1,nativeEvents a b lane isLeader++(storeResult a b lane isLeader).2)
theorem tail_count_segments (isLeader : Bool) : tailCount isLeader = 3+(7+storeCount isLeader) := by
  cases isLeader <;> rfl
theorem tail_run (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (tailCount isLeader) (at29 lane isLeader) =
      .ok (tailResult a b lane isLeader) := by
  rw [tail_count_segments,Wgmma.run_add,native_run]
  simp only [Except.bind]
  rw [Wgmma.run_add,address_run]
  simp only [Except.bind,store_run,List.nil_append]
  rfl
theorem tail_succeeds (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    (Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (tailCount isLeader) (at29 lane isLeader)).toOption.isSome = true := by
  rw [tail_run]
  rfl
theorem tail_complete_metadata (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    (((tailResult a b lane isLeader).1.base.scalar.core.thread.status == .done) &&
      ((Wgmma.pending (tailResult a b lane isLeader).1.ledger).length == 0)) = true :=
  store_complete_metadata a b lane isLeader
theorem tail_complete (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    Wgmma.Complete (tailResult a b lane isLeader).1 :=
  Wgmma.complete_of_metadata (tailResult a b lane isLeader).1 (tail_complete_metadata a b lane isLeader)
theorem total_count (lane : Wgmma.Lane) : count lane = 18+middleCount (leader lane)+tailCount (leader lane) := by
  by_cases h : lane.val = 0 <;> simp [count,leader,middleCount,tailCount,h]

end
end Ptx.Kernels.HopperStage
