import Ptx.Kernels.HopperStageCheckpoints

/-! Source segment from the leader branch to the WGMMA entry. Both paths are
checked with the actual generated instructions and payload length checks. The
chosen successful wait is source data; resource/memory legality is separate. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def middleCount (isLeader : Bool) : Nat := if isLeader then 11 else 6
def queryAt29 (isLeader : Bool) : Nat := if isLeader then 5 else 1
def at29 (lane : Wgmma.Lane) (isLeader : Bool) : Wgmma.State := {
  base := {scalar := {
    core := {
      thread := {pc := 29,regs := ("%ready",1)::prefixRegs lane (if isLeader then 1 else 0)}
      queries := queryAt29 isLeader
      generations := [(0,1)]}
    floats := zeroFloats
  }}
  ledger := {fenced := true,syncs := 1}
}
def fenceMark (lane : Wgmma.Lane) : Wgmma.Mark := ⟨28,0,Ampere.linearThread (ctx lane)/128⟩
def middleEvents (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) : List Wgmma.Event :=
  (if isLeader then [
    .base (.barrier ⟨⟨.shared .zero,0⟩,.init 1⟩),
    .base (.proxyFenceAsyncShared .zero),
    .base (.ampere (.ordinary (.barrierArrival 0 0))),
    .base (.ampere (.ordinary (.barrierReturn 0 0))),
    .base (.barrier ⟨⟨.shared .zero,0⟩,.arriveExpectTx 2304⟩),
    .base (.tmaIssue ⟨4096,aView,⟨0,0⟩,16,0,0,aPayload a⟩),
    .base (.tmaIssue ⟨4224,bView,⟨0,0⟩,2064,0,2,bPayload b⟩),
    .base (.barrier ⟨⟨.shared .zero,0⟩,.tryWaitParity 0 true⟩)
  ] else [
    .base (.ampere (.ordinary (.barrierArrival 0 0))),
    .base (.ampere (.ordinary (.barrierReturn 0 0))),
    .base (.barrier ⟨⟨.shared .zero,0⟩,.tryWaitParity 0 true⟩)
  ])++[.fence (fenceMark lane)]
theorem middle_run (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (middleCount isLeader)
      (at18 lane (if isLeader then 1 else 0)) = .ok (at29 lane isLeader,middleEvents a b lane isLeader) := by
  cases isLeader <;> rfl
theorem canonical_prefix_18 (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program 18 {} =
      .ok (at18 lane (if leader lane then 1 else 0),[]) := by
  rw [prefix_18,leader_word_value]
theorem source_prefix_29 (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (18+middleCount (leader lane)) {} =
      .ok (at29 lane (leader lane),middleEvents a b lane (leader lane)) := by
  rw [Wgmma.run_add,canonical_prefix_18]
  simp only [Except.bind,middle_run,List.nil_append]

end
end Ptx.Kernels.HopperStage
