import Ptx.Kernels.HopperDoubleBufferPhaseStep

/-! Actual stage/descriptor selection at PCs 45..54 for every tile number.
Fixed stage addresses are those computed by the generated prologue; the
prologue-to-loop invariant is a separate obligation. No oracle is restricted.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def selectionBindings (tile : Nat) : Bindings :=
  [("%slot",tile%2),("%bar0",0),("%bar1",8),
   ("%ad0",68720001025),("%bd0",68720001153),
   ("%ad1",68720001169),("%bd1",68720001297),
   ("%phase0",phaseZero tile),("%phase1",phaseOne tile)]
def SelectionReady (s : Wgmma.State) (tile : Nat) : Prop :=
  ∀ binding ∈ selectionBindings tile, lookup binding.1 s.base.scalar.core.thread.regs = some binding.2

def selectionPrefix (s : Wgmma.State) (tile : Nat) : Wgmma.State :=
  let s1 := Wgmma.integerAssign s (.setp .eq "%even" (.reg "%slot") (.imm 0)) "%even" (if tile%2 = 0 then 1 else 0)
  let s2 := Wgmma.integerAssign s1 (.mov 64 "%waitbar" (.reg "%bar0")) "%waitbar" (0)
  let s3 := Wgmma.integerAssign s2 (.mov 64 "%ad" (.reg "%ad0")) "%ad" (68720001025)
  let s4 := Wgmma.integerAssign s3 (.mov 64 "%bd" (.reg "%bd0")) "%bd" (68720001153)
  let s5 := Wgmma.integerAssign s4 (.mov 32 "%parity" (.reg "%phase0")) "%parity" (phaseZero tile)
  Wgmma.integerPC s5 (.branch "%even" true 55) (if tile%2 = 0 then 55 else 51)

def selectionState (s : Wgmma.State) (tile : Nat) : Wgmma.State :=
  if tile%2 = 0 then selectionPrefix s tile else
  let s6 := selectionPrefix s tile
  let s7 := Wgmma.integerAssign s6 (.mov 64 "%waitbar" (.reg "%bar1")) "%waitbar" (8)
  let s8 := Wgmma.integerAssign s7 (.mov 64 "%ad" (.reg "%ad1")) "%ad" (68720001169)
  let s9 := Wgmma.integerAssign s8 (.mov 64 "%bd" (.reg "%bd1")) "%bd" (68720001297)
  Wgmma.integerAssign s9 (.mov 32 "%parity" (.reg "%phase1")) "%parity" (phaseOne tile)
def selectionSteps (tile : Nat) : Nat := if tile%2 = 0 then 6 else 10

theorem selection_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State) (tile : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hregs : SelectionReady s tile) :
    Wgmma.run ctx oracle code (selectionSteps tile) s = .ok (selectionState s tile,[]) := by
  have hr0 : lookup "%slot" s.base.scalar.core.thread.regs = some (tile%2) := hregs ("%slot",tile%2) (by simp [selectionBindings])
  have hr1 : lookup "%bar0" s.base.scalar.core.thread.regs = some (0) := hregs ("%bar0",0) (by simp [selectionBindings])
  have hr2 : lookup "%bar1" s.base.scalar.core.thread.regs = some (8) := hregs ("%bar1",8) (by simp [selectionBindings])
  have hr3 : lookup "%ad0" s.base.scalar.core.thread.regs = some (68720001025) := hregs ("%ad0",68720001025) (by simp [selectionBindings])
  have hr4 : lookup "%bd0" s.base.scalar.core.thread.regs = some (68720001153) := hregs ("%bd0",68720001153) (by simp [selectionBindings])
  have hr5 : lookup "%ad1" s.base.scalar.core.thread.regs = some (68720001169) := hregs ("%ad1",68720001169) (by simp [selectionBindings])
  have hr6 : lookup "%bd1" s.base.scalar.core.thread.regs = some (68720001297) := hregs ("%bd1",68720001297) (by simp [selectionBindings])
  have hr7 : lookup "%phase0" s.base.scalar.core.thread.regs = some (phaseZero tile) := hregs ("%phase0",phaseZero tile) (by simp [selectionBindings])
  have hr8 : lookup "%phase1" s.base.scalar.core.thread.regs = some (phaseOne tile) := hregs ("%phase1",phaseOne tile) (by simp [selectionBindings])
  have hw0 : wrap 32 (phaseZero tile) = phaseZero tile := Nat.mod_eq_of_lt (by dsimp [phaseZero]; omega)
  have hw1 : wrap 32 (phaseOne tile) = phaseOne tile := Nat.mod_eq_of_lt (by dsimp [phaseOne]; omega)
  let s1 := Wgmma.integerAssign s (.setp .eq "%even" (.reg "%slot") (.imm 0)) "%even" (if tile%2 = 0 then 1 else 0)
  let s2 := Wgmma.integerAssign s1 (.mov 64 "%waitbar" (.reg "%bar0")) "%waitbar" (0)
  let s3 := Wgmma.integerAssign s2 (.mov 64 "%ad" (.reg "%ad0")) "%ad" (68720001025)
  let s4 := Wgmma.integerAssign s3 (.mov 64 "%bd" (.reg "%bd0")) "%bd" (68720001153)
  let s5 := Wgmma.integerAssign s4 (.mov 32 "%parity" (.reg "%phase0")) "%parity" (phaseZero tile)
  let s6 := Wgmma.integerPC s5 (.branch "%even" true 55) (if tile%2 = 0 then 55 else 51)
  have h1 : Wgmma.step ctx oracle code s = .ok (s1,[]) := by
    have hf : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.setp .eq "%even" (.reg "%slot") (.imm 0))))) := by simp [s1,hpc,code,Generated.hopper_double_buffer_gemm.program]
    have hs := Wgmma.eq_zero_step (ctx := ctx) (oracle := oracle) hr hf hp
      (show Ptx.eval ctx.id.tid.x s.base.scalar.core.thread (.reg "%slot") = .ok (tile%2) by simp [Ptx.eval,hr0]) (by omega)
    simpa only [s1] using hs
  have h2 : Wgmma.step ctx oracle code s1 = .ok (s2,[]) := by
    have hf : code[s1.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 64 "%waitbar" (.reg "%bar0"))))) := by simp [s1,s2,hpc,code,Generated.hopper_double_buffer_gemm.program]
    have hs := Wgmma.mov_step (ctx := ctx) (oracle := oracle) (by simp [s1,s2,hpc,hr]) hf (by simpa [s1,s2] using hp)
      (show Ptx.eval ctx.id.tid.x s1.base.scalar.core.thread (.reg "%bar0") = .ok (0) by simp [Ptx.eval,s1,s2,hr1])
    simpa only [s2,show wrap 64 0 = 0 from by decide] using hs
  have h3 : Wgmma.step ctx oracle code s2 = .ok (s3,[]) := by
    have hf : code[s2.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 64 "%ad" (.reg "%ad0"))))) := by simp [s1,s2,s3,hpc,code,Generated.hopper_double_buffer_gemm.program]
    have hs := Wgmma.mov_step (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,hpc,hr]) hf (by simpa [s1,s2,s3] using hp)
      (show Ptx.eval ctx.id.tid.x s2.base.scalar.core.thread (.reg "%ad0") = .ok (68720001025) by simp [Ptx.eval,s1,s2,s3,hr3])
    simpa only [s3,show wrap 64 68720001025 = 68720001025 from by decide] using hs
  have h4 : Wgmma.step ctx oracle code s3 = .ok (s4,[]) := by
    have hf : code[s3.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 64 "%bd" (.reg "%bd0"))))) := by simp [s1,s2,s3,s4,hpc,code,Generated.hopper_double_buffer_gemm.program]
    have hs := Wgmma.mov_step (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,s4,hpc,hr]) hf (by simpa [s1,s2,s3,s4] using hp)
      (show Ptx.eval ctx.id.tid.x s3.base.scalar.core.thread (.reg "%bd0") = .ok (68720001153) by simp [Ptx.eval,s1,s2,s3,s4,hr4])
    simpa only [s4,show wrap 64 68720001153 = 68720001153 from by decide] using hs
  have h5 : Wgmma.step ctx oracle code s4 = .ok (s5,[]) := by
    have hf : code[s4.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 32 "%parity" (.reg "%phase0"))))) := by simp [s1,s2,s3,s4,s5,hpc,code,Generated.hopper_double_buffer_gemm.program]
    have hs := Wgmma.mov_step (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,s4,s5,hpc,hr]) hf (by simpa [s1,s2,s3,s4,s5] using hp)
      (show Ptx.eval ctx.id.tid.x s4.base.scalar.core.thread (.reg "%phase0") = .ok (phaseZero tile) by simp [Ptx.eval,s1,s2,s3,s4,s5,hr7])
    simpa only [s5,hw0] using hs
  have h6 : Wgmma.step ctx oracle code s5 = .ok (s6,[]) := by
    have hf : code[s5.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.branch "%even" true 55)))) := by simp [s1,s2,s3,s4,s5,s6,hpc,code,Generated.hopper_double_buffer_gemm.program]
    have hs := Wgmma.branch_step (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,s4,s5,s6,hpc,hr]) hf (by simpa [s1,s2,s3,s4,s5,s6] using hp)
      (show lookup "%even" s5.base.scalar.core.thread.regs = some (if tile%2 = 0 then 1 else 0) by simp [s1,s2,s3,s4,s5,s6])
    by_cases ht : tile%2 = 0 <;> simpa [s1,s2,s3,s4,s5,s6,ht,hpc] using hs
  by_cases ht : tile%2 = 0
  · dsimp only [s1,s2,s3,s4,s5,s6] at h1 h2 h3 h4 h5 h6
    simp only [ht,ite_true] at h1 h2 h3 h4 h5 h6
    simpa only [selectionSteps,selectionState,ht,ite_true,selectionPrefix,Wgmma.run,h1,h2,h3,h4,h5,h6,Except.bind,List.nil_append]
  ·
    let s7 := Wgmma.integerAssign s6 (.mov 64 "%waitbar" (.reg "%bar1")) "%waitbar" (8)
    let s8 := Wgmma.integerAssign s7 (.mov 64 "%ad" (.reg "%ad1")) "%ad" (68720001169)
    let s9 := Wgmma.integerAssign s8 (.mov 64 "%bd" (.reg "%bd1")) "%bd" (68720001297)
    let s10 := Wgmma.integerAssign s9 (.mov 32 "%parity" (.reg "%phase1")) "%parity" (phaseOne tile)
    have h7 : Wgmma.step ctx oracle code s6 = .ok (s7,[]) := by
      have hf : code[s6.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 64 "%waitbar" (.reg "%bar1"))))) := by simp [s1,s2,s3,s4,s5,s6,s7,ht,hpc,code,Generated.hopper_double_buffer_gemm.program]
      have hs := Wgmma.mov_step (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,s4,s5,s6,s7,ht,hpc,hr]) hf (by simpa [s1,s2,s3,s4,s5,s6,s7] using hp)
        (show Ptx.eval ctx.id.tid.x s6.base.scalar.core.thread (.reg "%bar1") = .ok (8) by simp [Ptx.eval,s1,s2,s3,s4,s5,s6,s7,hr2])
      simpa only [s7,show wrap 64 8 = 8 from by decide] using hs
    have h8 : Wgmma.step ctx oracle code s7 = .ok (s8,[]) := by
      have hf : code[s7.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 64 "%ad" (.reg "%ad1"))))) := by simp [s1,s2,s3,s4,s5,s6,s7,s8,ht,hpc,code,Generated.hopper_double_buffer_gemm.program]
      have hs := Wgmma.mov_step (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,s4,s5,s6,s7,s8,ht,hpc,hr]) hf (by simpa [s1,s2,s3,s4,s5,s6,s7,s8] using hp)
        (show Ptx.eval ctx.id.tid.x s7.base.scalar.core.thread (.reg "%ad1") = .ok (68720001169) by simp [Ptx.eval,s1,s2,s3,s4,s5,s6,s7,s8,hr5])
      simpa only [s8,show wrap 64 68720001169 = 68720001169 from by decide] using hs
    have h9 : Wgmma.step ctx oracle code s8 = .ok (s9,[]) := by
      have hf : code[s8.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 64 "%bd" (.reg "%bd1"))))) := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,ht,hpc,code,Generated.hopper_double_buffer_gemm.program]
      have hs := Wgmma.mov_step (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,ht,hpc,hr]) hf (by simpa [s1,s2,s3,s4,s5,s6,s7,s8,s9] using hp)
        (show Ptx.eval ctx.id.tid.x s8.base.scalar.core.thread (.reg "%bd1") = .ok (68720001297) by simp [Ptx.eval,s1,s2,s3,s4,s5,s6,s7,s8,s9,hr6])
      simpa only [s9,show wrap 64 68720001297 = 68720001297 from by decide] using hs
    have h10 : Wgmma.step ctx oracle code s9 = .ok (s10,[]) := by
      have hf : code[s9.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 32 "%parity" (.reg "%phase1"))))) := by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ht,hpc,code,Generated.hopper_double_buffer_gemm.program]
      have hs := Wgmma.mov_step (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,ht,hpc,hr]) hf (by simpa [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10] using hp)
        (show Ptx.eval ctx.id.tid.x s9.base.scalar.core.thread (.reg "%phase1") = .ok (phaseOne tile) by simp [Ptx.eval,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,hr8])
      simpa only [s10,hw1] using hs
    dsimp only [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simp only [ht,ite_false] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    simpa only [selectionSteps,selectionState,ht,ite_false,selectionPrefix,Wgmma.run,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,Except.bind,List.nil_append]

@[simp] theorem selectionState_pc (s : Wgmma.State) (tile : Nat) :
    (selectionState s tile).base.scalar.core.thread.pc = 55 := by
  by_cases ht : tile%2 = 0 <;> simp [selectionState,selectionPrefix,ht]
@[simp] theorem selectionState_queries (s : Wgmma.State) (tile : Nat) :
    (selectionState s tile).base.scalar.core.queries = s.base.scalar.core.queries := by
  by_cases ht : tile%2 = 0 <;> simp [selectionState,selectionPrefix,ht]
@[simp] theorem selectionState_status (s : Wgmma.State) (tile : Nat) :
    (selectionState s tile).base.scalar.core.thread.status = s.base.scalar.core.thread.status := by
  by_cases ht : tile%2 = 0 <;> simp [selectionState,selectionPrefix,ht]
@[simp] theorem selectionState_pending (s : Wgmma.State) (tile : Nat) :
    Wgmma.pending (selectionState s tile).ledger = Wgmma.pending s.ledger := by
  by_cases ht : tile%2 = 0 <;> simp [selectionState,selectionPrefix,ht]

theorem selectionState_operands (s : Wgmma.State) (tile : Nat) :
    lookup "%waitbar" (selectionState s tile).base.scalar.core.thread.regs = some (barrierAddress (stage tile)) ∧
    lookup "%ad" (selectionState s tile).base.scalar.core.thread.regs = some (aDescriptor (stage tile)) ∧
    lookup "%bd" (selectionState s tile).base.scalar.core.thread.regs = some (bDescriptor (stage tile)) ∧
    lookup "%parity" (selectionState s tile).base.scalar.core.thread.regs = some (expectedParity tile) := by
  have hp := selected_expected_parity tile
  have hs : tile%2 = 0 ∨ tile%2 = 1 := by omega
  rcases hs with ht | ht
  all_goals simp [selectionState,selectionPrefix,stage,ht,barrierAddress,aDescriptor,bDescriptor,
    aBase,bBase,Wgmma.MatrixDescriptor.encode] at hp ⊢
  all_goals exact hp

theorem selectionState_nat_frame (s : Wgmma.State) (tile : Nat) (name : String)
    (hn : name ∉ ["%even","%waitbar","%ad","%bd","%parity"]) :
    lookup name (selectionState s tile).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := by
  have hh : name ≠ "%even" ∧ name ≠ "%waitbar" ∧ name ≠ "%ad" ∧ name ≠ "%bd" ∧ name ≠ "%parity" := by simpa using hn
  by_cases ht : tile%2 = 0 <;> simp [selectionState,selectionPrefix,ht,hh]

theorem selectionState_float_frame (s : Wgmma.State) (tile : Nat) (name : String)
    (hx : name ∉ ["%even","%waitbar","%ad","%bd","%parity"])
    (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (selectionState s tile).base.scalar.floats = declarationLookup name s.base.scalar.floats := by
  have hh : name ≠ "%even" ∧ name ≠ "%waitbar" ∧ name ≠ "%ad" ∧ name ≠ "%bd" ∧ name ≠ "%parity" := by simpa using hx
  by_cases ht : tile%2 = 0
  all_goals simp only [selectionState,selectionPrefix,ht,ite_true,ite_false,
    Wgmma.integerAssign,Wgmma.integerPC,Wgmma.ordinaryState,Ampere.intAssign,Ampere.intPC]
  all_goals simp [Scalar.intAssign_float,Scalar.intPC_float,hh,hn]

@[simp] theorem selectionState_even (s : Wgmma.State) (tile : Nat) :
    lookup "%even" (selectionState s tile).base.scalar.core.thread.regs = some (if tile%2 = 0 then 1 else 0) := by
  by_cases ht : tile%2 = 0 <;> simp [selectionState,selectionPrefix,ht]

end
end Ptx.Kernels.HopperDoubleBuffer
