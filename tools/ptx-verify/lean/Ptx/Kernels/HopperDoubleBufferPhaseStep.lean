import Ptx.Kernels.HopperDoubleBufferWait

/-! Generated-source phase updates at PCs 57..60, for an arbitrary tile and
an arbitrary running lane state with no outstanding WGMMA call. The loop
phase functions are conclusions of execution, rather than oracle replies. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def phaseState (s : Wgmma.State) (tile : Nat) : Wgmma.State :=
  if tile%2 = 0 then
    let s1 := Wgmma.integerPC s (.branch "%even" false 60) 58
    let s2 := Wgmma.integerAssign s1 (.bin .sub 32 32 "%phase0" (.imm 1) (.reg "%phase0")) "%phase0" (1-phaseZero tile)
    Wgmma.integerPC s2 (.branch "%even" true 61) 61
  else
    let s1 := Wgmma.integerPC s (.branch "%even" false 60) 60
    Wgmma.integerAssign s1 (.bin .sub 32 32 "%phase1" (.imm 1) (.reg "%phase1")) "%phase1" (1-phaseOne tile)
def phaseSteps (tile : Nat) : Nat := if tile%2 = 0 then 3 else 2

theorem phase_update_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State) (tile : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 57)
    (hp : Wgmma.pending s.ledger = [])
    (he : lookup "%even" s.base.scalar.core.thread.regs = some (if tile%2 = 0 then 1 else 0))
    (hz : lookup "%phase0" s.base.scalar.core.thread.regs = some (phaseZero tile))
    (ho : lookup "%phase1" s.base.scalar.core.thread.regs = some (phaseOne tile)) :
    Wgmma.run ctx oracle code (phaseSteps tile) s = .ok (phaseState s tile,[]) := by
  by_cases ht : tile%2 = 0
  · let s1 := Wgmma.integerPC s (.branch "%even" false 60) 58
    let s2 := Wgmma.integerAssign s1 (.bin .sub 32 32 "%phase0" (.imm 1) (.reg "%phase0")) "%phase0" (1-phaseZero tile)
    have h0 : Wgmma.step ctx oracle code s = .ok (s1,[]) := by
      simpa [s1,ht,hpc] using Wgmma.branch_step (ctx := ctx) (oracle := oracle) hr
        (show code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.branch "%even" false 60)))) by simp [hpc,code,Generated.hopper_double_buffer_gemm.program]) hp he
    have h1 : Wgmma.step ctx oracle code s1 = .ok (s2,[]) := by
      apply Wgmma.flip_step (by simp [s1,hr])
        (by simp [s1,code,Generated.hopper_double_buffer_gemm.program])
        (by simpa [s1] using hp)
        (by simpa [s1] using hz)
      exact Nat.mod_lt _ (by decide)
    have h2 : Wgmma.step ctx oracle code s2 = .ok (phaseState s tile,[]) := by
      have hlookup : lookup "%even" s2.base.scalar.core.thread.regs = some 1 := by simp [s2,s1,he,ht]
      simpa [phaseState,ht,s1,s2] using Wgmma.branch_step (ctx := ctx) (oracle := oracle)
        (by simp [s2,s1,hr])
        (show code[s2.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.branch "%even" true 61)))) by simp [s2,s1,code,Generated.hopper_double_buffer_gemm.program])
        (by simpa [s2,s1] using hp) hlookup
    simp only [phaseSteps,ht,ite_true,Wgmma.run,h0,h1,h2,Except.bind,List.nil_append]
  · let s1 := Wgmma.integerPC s (.branch "%even" false 60) 60
    have h0 : Wgmma.step ctx oracle code s = .ok (s1,[]) := by
      simpa [s1,ht,hpc] using Wgmma.branch_step (ctx := ctx) (oracle := oracle) hr
        (show code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.branch "%even" false 60)))) by simp [hpc,code,Generated.hopper_double_buffer_gemm.program]) hp he
    have h1 : Wgmma.step ctx oracle code s1 = .ok (phaseState s tile,[]) := by
      simpa [phaseState,ht,s1] using Wgmma.flip_step (ctx := ctx) (oracle := oracle)
        (by simp [s1,hr])
        (show code[s1.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.bin .sub 32 32 "%phase1" (.imm 1) (.reg "%phase1"))))) by simp [s1,code,Generated.hopper_double_buffer_gemm.program])
        (by simpa [s1] using hp) (show lookup "%phase1" s1.base.scalar.core.thread.regs = some (phaseOne tile) by simpa [s1] using ho)
        (Nat.mod_lt _ (by decide))
    simp only [phaseSteps,ht,ite_false,Wgmma.run,h0,h1,Except.bind,List.nil_append]

@[simp] theorem phaseState_pc (s : Wgmma.State) (tile : Nat) :
    (phaseState s tile).base.scalar.core.thread.pc = 61 := by
  by_cases ht : tile%2 = 0 <;> simp [phaseState,ht]
@[simp] theorem phaseState_status (s : Wgmma.State) (tile : Nat) :
    (phaseState s tile).base.scalar.core.thread.status = s.base.scalar.core.thread.status := by
  by_cases ht : tile%2 = 0 <;> simp [phaseState,ht]
@[simp] theorem phaseState_queries (s : Wgmma.State) (tile : Nat) :
    (phaseState s tile).base.scalar.core.queries = s.base.scalar.core.queries := by
  by_cases ht : tile%2 = 0 <;> simp [phaseState,ht]
@[simp] theorem phaseState_pending (s : Wgmma.State) (tile : Nat) :
    Wgmma.pending (phaseState s tile).ledger = Wgmma.pending s.ledger := by
  by_cases ht : tile%2 = 0 <;> simp [phaseState,ht]

theorem phaseState_phases (s : Wgmma.State) (tile : Nat)
    (hz : lookup "%phase0" s.base.scalar.core.thread.regs = some (phaseZero tile))
    (ho : lookup "%phase1" s.base.scalar.core.thread.regs = some (phaseOne tile)) :
    lookup "%phase0" (phaseState s tile).base.scalar.core.thread.regs = some (phaseZero (tile+1)) ∧
    lookup "%phase1" (phaseState s tile).base.scalar.core.thread.regs = some (phaseOne (tile+1)) := by
  by_cases ht : tile%2 = 0
  · obtain ⟨hz',ho'⟩ := even_phase_transition ht
    simp [phaseState,ht,hz,ho,hz',ho']
  · obtain ⟨ho',hz'⟩ := odd_phase_transition ht
    simp [phaseState,ht,hz,ho,hz',ho']

theorem phaseState_nat_frame (s : Wgmma.State) (tile : Nat) (name : String)
    (hz : name ≠ "%phase0") (ho : name ≠ "%phase1") :
    lookup name (phaseState s tile).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := by
  by_cases ht : tile%2 = 0 <;> simp [phaseState,ht,hz,ho]

theorem phaseState_float_frame (s : Wgmma.State) (tile : Nat) (name : String)
    (hz : name ≠ "%phase0") (ho : name ≠ "%phase1")
    (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (phaseState s tile).base.scalar.floats = declarationLookup name s.base.scalar.floats := by
  by_cases ht : tile%2 = 0
  · simp only [phaseState,ht,ite_true]
    rw [Wgmma.integerPC_float, Wgmma.integerAssign_float, Wgmma.integerPC_float]
    all_goals simp [hz,hn]
  · simp only [phaseState,ht,ite_false]
    rw [Wgmma.integerAssign_float,Wgmma.integerPC_float]
    all_goals simp [ho,hn]

end
end Ptx.Kernels.HopperDoubleBuffer
