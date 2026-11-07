import Ptx.Kernels.HopperDoubleBufferHeader
import Ptx.Hopper.WgmmaControl

/-! Actual PCs 80..84: emit the reuse rendezvous, toggle the stage, increment
K-tile and either continue at PC 45 or enter output at PC 85. No source-level
barrier here establishes graph admission or completes outstanding WGMMA work.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def advanceState (s : Wgmma.State) (tile tiles : Nat) : Wgmma.State :=
  let s1 := Wgmma.barrierState s 2
  let s2 := Wgmma.integerAssign s1 (.bin .sub 32 32 "%slot" (.imm 1) (.reg "%slot")) "%slot" (1-tile%2)
  let s3 := Wgmma.integerAssign s2 (.bin .add 32 32 "%tile" (.reg "%tile") (.imm 1)) "%tile" (tile+1)
  let s4 := Wgmma.integerAssign s3 (.setp .lt "%more" (.reg "%tile") (.reg "%tiles")) "%more" (if tile+1 < tiles then 1 else 0)
  Wgmma.integerPC s4 (.branch "%more" true 45) (if tile+1 < tiles then 45 else 85)
def advanceEvents (s : Wgmma.State) : List Wgmma.Event :=
  [.base (.ampere (.ordinary (.barrierArrival 2 (Ptx.Event.generation s.base.scalar.core 2)))),
   .base (.ampere (.ordinary (.barrierReturn 2 (Ptx.Event.generation s.base.scalar.core 2))))]

theorem advance_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State) (tile tiles : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 80)
    (hp : Wgmma.pending s.ledger = [])
    (hs : lookup "%slot" s.base.scalar.core.thread.regs = some (tile%2))
    (ht : lookup "%tile" s.base.scalar.core.thread.regs = some tile)
    (hb : lookup "%tiles" s.base.scalar.core.thread.regs = some tiles)
    (hlt : tile < tiles) (hbound : tiles < 2^32) :
    Wgmma.run ctx oracle code 5 s = .ok (advanceState s tile tiles,advanceEvents s) := by
  let s1 := Wgmma.barrierState s 2
  let s2 := Wgmma.integerAssign s1 (.bin .sub 32 32 "%slot" (.imm 1) (.reg "%slot")) "%slot" (1-tile%2)
  let s3 := Wgmma.integerAssign s2 (.bin .add 32 32 "%tile" (.reg "%tile") (.imm 1)) "%tile" (tile+1)
  let s4 := Wgmma.integerAssign s3 (.setp .lt "%more" (.reg "%tile") (.reg "%tiles")) "%more" (if tile+1 < tiles then 1 else 0)
  have h0 : Wgmma.step ctx oracle code s = .ok (s1,advanceEvents s) := by
    exact Wgmma.barrier_step hr (by simp [hpc,code,Generated.hopper_double_buffer_gemm.program])
  have h1 : Wgmma.step ctx oracle code s1 = .ok (s2,[]) := by
    apply Wgmma.flip_step (by simp [s1,hr])
      (by simp [s1,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1] using hp) (by simpa [s1] using hs)
    omega
  have h2 : Wgmma.step ctx oracle code s2 = .ok (s3,[]) := by
    exact Wgmma.increment_step (by simp [s2,s1,hr])
      (by simp [s2,s1,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s2,s1] using hp) (by simpa [s2,s1] using ht) (by omega)
  have h3 : Wgmma.step ctx oracle code s3 = .ok (s4,[]) := by
    apply Wgmma.lt_step (by simp [s3,s2,s1,hr])
      (by simp [s3,s2,s1,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s3,s2,s1] using hp)
      (by simp [s3]) (by simpa [s3,s2,s1] using hb) (by omega) hbound
  have h4 : Wgmma.step ctx oracle code s4 = .ok (advanceState s tile tiles,[]) := by
    have hh := Wgmma.branch_step (ctx := ctx) (oracle := oracle)
      (by simp [s4,s3,s2,s1,hr])
      (show code[s4.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.branch "%more" true 45)))) by simp [s4,s3,s2,s1,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s4,s3,s2,s1] using hp)
      (show lookup "%more" s4.base.scalar.core.thread.regs = some (if tile+1 < tiles then 1 else 0) by simp [s4])
    by_cases h : tile+1 < tiles <;> simpa [advanceState,s4,s3,s2,s1,h,hpc] using hh
  dsimp only [s4,s3,s2,s1] at h0 h1 h2 h3 h4
  simp only [Wgmma.run,h0,h1,h2,h3,h4,Except.bind,List.nil_append,List.append_nil]

@[simp] theorem advanceState_pc (s : Wgmma.State) (tile tiles : Nat) :
    (advanceState s tile tiles).base.scalar.core.thread.pc = if tile+1 < tiles then 45 else 85 := rfl
@[simp] theorem advanceState_queries (s : Wgmma.State) (tile tiles : Nat) :
    (advanceState s tile tiles).base.scalar.core.queries = s.base.scalar.core.queries := rfl
@[simp] theorem advanceState_status (s : Wgmma.State) (tile tiles : Nat) :
    (advanceState s tile tiles).base.scalar.core.thread.status = s.base.scalar.core.thread.status := rfl
@[simp] theorem advanceState_pending (s : Wgmma.State) (tile tiles : Nat) :
    Wgmma.pending (advanceState s tile tiles).ledger = Wgmma.pending s.ledger := rfl

theorem advanceState_counters (s : Wgmma.State) (tile tiles : Nat) :
    lookup "%tile" (advanceState s tile tiles).base.scalar.core.thread.regs = some (tile+1) ∧
    lookup "%slot" (advanceState s tile tiles).base.scalar.core.thread.regs = some (stage (tile+1)).val := by
  simp [advanceState,selected_stage_toggles,stage]
  exact selected_stage_toggles tile |>.symm

theorem advanceState_generation (s : Wgmma.State) (tile tiles : Nat) :
    Ptx.Event.generation (advanceState s tile tiles).base.scalar.core 2 = Ptx.Event.generation s.base.scalar.core 2+1 :=
  Wgmma.barrierState_generation s 2

theorem advanceState_nat_frame (s : Wgmma.State) (tile tiles : Nat) (name : String)
    (hn : name ∉ ["%slot","%tile","%more"]) :
    lookup name (advanceState s tile tiles).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := by
  have hh : name ≠ "%slot" ∧ name ≠ "%tile" ∧ name ≠ "%more" := by simpa using hn
  simp [advanceState,hh]

theorem advanceState_float_frame (s : Wgmma.State) (tile tiles : Nat) (name : String)
    (hx : name ∉ ["%slot","%tile","%more"]) (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (advanceState s tile tiles).base.scalar.floats = declarationLookup name s.base.scalar.floats := by
  have hh : name ≠ "%slot" ∧ name ≠ "%tile" ∧ name ≠ "%more" := by simpa using hx
  simp only [advanceState,Wgmma.integerAssign,Wgmma.integerPC,Wgmma.ordinaryState,
    Wgmma.barrierState,Ampere.intAssign,Ampere.intPC]
  simp [Scalar.intAssign_float,Scalar.intPC_float,hh,hn,Ampere.barrier_float]

end
end Ptx.Kernels.HopperDoubleBuffer
