import Ptx.Kernels.HopperStageTransfer

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def accumulatorInput (slot : Wgmma.Slot) : ℝ := if slot.val = 0 then zeroLiteral.value
  else if slot.val = 1 then zeroLiteral.value else if slot.val = 2 then zeroLiteral.value else zeroLiteral.value
def stageCall (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) : Wgmma.Call :=
  Wgmma.makeCall (ctx lane) (at29 lane isLeader) (oracle a b lane) ⟨"%d0","%d1","%d2","%d3"⟩
    68720001025 68720001153 true accumulatorInput
def at32 (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) : Wgmma.State := {
  base := {scalar := {
    core := {
      thread := {pc := 32,regs := ("%ready",1)::prefixRegs lane (if isLeader then 1 else 0)}
      queries := queryAt29 isLeader+2
      generations := [(0,1)]}
    floats := [("%d0",(.f32,(stageCall a b lane isLeader).output 0)),("%d1",(.f32,(stageCall a b lane isLeader).output 1)),
      ("%d2",(.f32,(stageCall a b lane isLeader).output 2)),("%d3",(.f32,(stageCall a b lane isLeader).output 3))]
  }}
  ledger := {fenced := true,groups := 1,completed := 1,calls := [stageCall a b lane isLeader],syncs := 4}
}
def nativeEvents (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) : List Wgmma.Event := [
  .mma ⟨29,1,Ampere.linearThread (ctx lane)/128⟩ (stageCall a b lane isLeader),
  .commit ⟨30,2,Ampere.linearThread (ctx lane)/128⟩ 0,
  .wait ⟨31,3,Ampere.linearThread (ctx lane)/128⟩ 1 0 0 1 (queryAt29 isLeader+1)]
theorem native_run (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program 3 (at29 lane isLeader) =
      .ok (at32 a b lane isLeader,nativeEvents a b lane isLeader) := by rfl

end
end Ptx.Kernels.HopperStage
