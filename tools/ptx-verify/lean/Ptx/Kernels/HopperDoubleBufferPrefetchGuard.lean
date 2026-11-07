import Ptx.Kernels.HopperDoubleBufferAdvance

/-! Generated PCs 61..64. Last-tile execution skips prefetch; otherwise only
an elected producer enters PC 65. Election is an explicit loop invariant,
not a claim that an arbitrary supplied context is the producer. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def prefetchGuardPrefix (s : Wgmma.State) (tile tiles : Nat) : Wgmma.State :=
  let s1 := Wgmma.integerAssign s (.bin .add 32 32 "%next" (.reg "%tile") (.imm 1)) "%next" (tile+1)
  let s2 := Wgmma.integerAssign s1 (.setp .lt "%more" (.reg "%next") (.reg "%tiles")) "%more" (if tile+1 < tiles then 1 else 0)
  Wgmma.integerPC s2 (.branch "%more" false 76) (if tile+1 < tiles then 64 else 76)
def prefetchGuardState (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) : Wgmma.State :=
  if tile+1 < tiles then Wgmma.integerPC (prefetchGuardPrefix s tile tiles)
    (.branch "%leader" false 76) (if leader then 65 else 76)
  else prefetchGuardPrefix s tile tiles
def prefetchGuardSteps (tile tiles : Nat) : Nat := if tile+1 < tiles then 4 else 3

theorem prefetch_guard_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle)
    (s : Wgmma.State) (tile tiles : Nat) (leader : Bool)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 61)
    (hp : Wgmma.pending s.ledger = [])
    (ht : lookup "%tile" s.base.scalar.core.thread.regs = some tile)
    (hb : lookup "%tiles" s.base.scalar.core.thread.regs = some tiles)
    (hl : lookup "%leader" s.base.scalar.core.thread.regs = some (if leader then 1 else 0))
    (hlt : tile < tiles) (hbound : tiles < 2^32) :
    Wgmma.run ctx oracle code (prefetchGuardSteps tile tiles) s =
      .ok (prefetchGuardState s tile tiles leader,[]) := by
  let s1 := Wgmma.integerAssign s (.bin .add 32 32 "%next" (.reg "%tile") (.imm 1)) "%next" (tile+1)
  let s2 := Wgmma.integerAssign s1 (.setp .lt "%more" (.reg "%next") (.reg "%tiles")) "%more" (if tile+1 < tiles then 1 else 0)
  let s3 := prefetchGuardPrefix s tile tiles
  have h0 : Wgmma.step ctx oracle code s = .ok (s1,[]) := by
    exact Wgmma.increment_step hr (by simp [hpc,code,Generated.hopper_double_buffer_gemm.program]) hp ht (by omega)
  have h1 : Wgmma.step ctx oracle code s1 = .ok (s2,[]) := by
    apply Wgmma.lt_step (by simp [s1,hr])
      (by simp [s1,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1] using hp) (by simp [s1]) (by simpa [s1] using hb) (by omega) hbound
  have h2 : Wgmma.step ctx oracle code s2 = .ok (s3,[]) := by
    have hh := Wgmma.branch_step (ctx := ctx) (oracle := oracle) (by simp [s2,s1,hr])
      (show code[s2.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.branch "%more" false 76)))) by simp [s2,s1,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s2,s1] using hp)
      (show lookup "%more" s2.base.scalar.core.thread.regs = some (if tile+1 < tiles then 1 else 0) by simp [s2])
    by_cases h : tile+1 < tiles <;> simpa [s3,prefetchGuardPrefix,s2,s1,h,hpc] using hh
  by_cases h : tile+1 < tiles
  · have h3 : Wgmma.step ctx oracle code s3 = .ok (prefetchGuardState s tile tiles leader,[]) := by
      have hh := Wgmma.branch_step (ctx := ctx) (oracle := oracle)
        (by simp [s3,prefetchGuardPrefix,hr])
        (show code[s3.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.branch "%leader" false 76)))) by simp [s3,prefetchGuardPrefix,h,code,Generated.hopper_double_buffer_gemm.program])
        (by simpa [s3,prefetchGuardPrefix] using hp)
        (show lookup "%leader" s3.base.scalar.core.thread.regs = some (if leader then 1 else 0) by simpa [s3,prefetchGuardPrefix] using hl)
      cases leader <;> simpa [prefetchGuardState,h,s3,prefetchGuardPrefix] using hh
    dsimp only [s3,s2,s1] at h0 h1 h2 h3
    simp only [h,ite_true] at h0 h1 h2
    simp only [prefetchGuardSteps,h,ite_true,Wgmma.run,h0,h1,h2,h3,Except.bind,List.nil_append]
  · dsimp only [s3,s2,s1] at h0 h1 h2
    simp only [h,ite_false] at h0 h1 h2
    simp only [prefetchGuardSteps,prefetchGuardState,h,ite_false,Wgmma.run,h0,h1,h2,Except.bind,List.nil_append]

@[simp] theorem prefetchGuardState_pc (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) :
    (prefetchGuardState s tile tiles leader).base.scalar.core.thread.pc =
      if tile+1 < tiles then (if leader then 65 else 76) else 76 := by
  by_cases h : tile+1 < tiles <;> simp [prefetchGuardState,prefetchGuardPrefix,h]
@[simp] theorem prefetchGuardState_queries (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) :
    (prefetchGuardState s tile tiles leader).base.scalar.core.queries = s.base.scalar.core.queries := by
  by_cases h : tile+1 < tiles <;> simp [prefetchGuardState,prefetchGuardPrefix,h]
@[simp] theorem prefetchGuardState_status (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) :
    (prefetchGuardState s tile tiles leader).base.scalar.core.thread.status = s.base.scalar.core.thread.status := by
  by_cases h : tile+1 < tiles <;> simp [prefetchGuardState,prefetchGuardPrefix,h]
@[simp] theorem prefetchGuardState_pending (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) :
    Wgmma.pending (prefetchGuardState s tile tiles leader).ledger = Wgmma.pending s.ledger := by
  by_cases h : tile+1 < tiles <;> simp [prefetchGuardState,prefetchGuardPrefix,h]

theorem prefetchGuardState_next (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) :
    lookup "%next" (prefetchGuardState s tile tiles leader).base.scalar.core.thread.regs = some (tile+1) := by
  by_cases h : tile+1 < tiles <;> simp [prefetchGuardState,prefetchGuardPrefix,h]

theorem prefetchGuardState_nat_frame (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) (name : String)
    (hn : name ∉ ["%next","%more"]) :
    lookup name (prefetchGuardState s tile tiles leader).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := by
  have hh : name ≠ "%next" ∧ name ≠ "%more" := by simpa using hn
  by_cases h : tile+1 < tiles <;> simp [prefetchGuardState,prefetchGuardPrefix,h,hh]

theorem prefetchGuardState_float_frame (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) (name : String)
    (hx : name ∉ ["%next","%more"]) (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (prefetchGuardState s tile tiles leader).base.scalar.floats = declarationLookup name s.base.scalar.floats := by
  have hh : name ≠ "%next" ∧ name ≠ "%more" := by simpa using hx
  by_cases h : tile+1 < tiles
  all_goals simp only [prefetchGuardState,prefetchGuardPrefix,h,ite_true,ite_false,
    Wgmma.integerAssign,Wgmma.integerPC,Wgmma.ordinaryState,Ampere.intAssign,Ampere.intPC]
  all_goals simp [Scalar.intAssign_float,Scalar.intPC_float,hh,hn]

end
end Ptx.Kernels.HopperDoubleBuffer
