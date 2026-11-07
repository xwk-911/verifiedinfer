import Ptx.Kernels.HopperStageNative

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def rowFirst (lane : Wgmma.Lane) : Nat := wrap 32 (wrap 32 (zWord lane)*16)
def rowFinal (lane : Wgmma.Lane) : Nat := wrap 32 (wrap 32 (rowFirst lane)+wrap 32 (yWord lane))
def colFinal (lane : Wgmma.Lane) : Nat := wrap 32 (wrap 32 (xWord lane)*2)
def linearFirst (lane : Wgmma.Lane) : Nat := wrap 32 (wrap 32 (rowFinal lane)*8)
def linearFinal (lane : Wgmma.Lane) : Nat := wrap 32 (wrap 32 (linearFirst lane)+wrap 32 (colFinal lane))
def offsetFinal (lane : Wgmma.Lane) : Nat := wrap 64 (wrap 32 (linearFinal lane)*4)
def outFinal (lane : Wgmma.Lane) : Nat := wrap 64 (wrap 64 (wrap 64 8192)+wrap 64 (offsetFinal lane))
def finalRegs (lane : Wgmma.Lane) (isLeader : Bool) : Bindings := [
  ("%out",outFinal lane),("%offset",offsetFinal lane),("%linear",linearFinal lane),("%col",colFinal lane),("%row",rowFinal lane)]++
  (("%ready",1)::prefixRegs lane (if isLeader then 1 else 0)).filter (fun binding => binding.1 != "%out")
def at39 (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) : Wgmma.State := {
  base := {(at32 a b lane isLeader).base with scalar := {(at32 a b lane isLeader).base.scalar with
    core := {(at32 a b lane isLeader).base.scalar.core with thread := {pc := 39,regs := finalRegs lane isLeader}}}}
  ledger := {(at32 a b lane isLeader).ledger with dirty := dirtyAt ((List.range 7).map (fun pc => pc+32))}
}
theorem address_run (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program 7 (at32 a b lane isLeader) =
      .ok (at39 a b lane isLeader,[]) := by rfl

end
end Ptx.Kernels.HopperStage
