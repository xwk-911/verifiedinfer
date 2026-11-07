import Ptx.Kernels.HopperDoubleBufferPhases
import Ptx.Hopper.WgmmaInteger

/-! The actual wait/test back edge at PCs 55/56. Both oracle answers are
executed; an arbitrary finite unsuccessful prefix is allowed. These local
source facts neither establish graph admission nor promise eventual success. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
abbrev code := Generated.hopper_double_buffer_gemm.program

def waitInstruction : Hopper.Instr := .tryWaitParity "%ready" ⟨.reg "%waitbar",0⟩ (.reg "%parity")
def waitState (s : Wgmma.State) (answer : Bool) : Wgmma.State :=
  Wgmma.ordinaryState s waitInstruction (Hopper.waitState s.base "%ready" answer)
def testedState (s : Wgmma.State) (answer : Bool) : Wgmma.State :=
  Wgmma.integerPC (waitState s answer) (.branch "%ready" false 55) (if answer then 57 else 55)
def waitEvent (ctx : Scalar.Context) (bar parity : Nat) (answer : Bool) : Wgmma.Event :=
  .base (.barrier ⟨⟨.shared ctx.id.cta,bar⟩,.tryWaitParity parity answer⟩)

@[simp] theorem waitState_status (s : Wgmma.State) (answer : Bool) :
    (waitState s answer).base.scalar.core.thread.status = s.base.scalar.core.thread.status := rfl
@[simp] theorem waitState_pc (s : Wgmma.State) (answer : Bool) :
    (waitState s answer).base.scalar.core.thread.pc = s.base.scalar.core.thread.pc+1 := rfl
@[simp] theorem waitState_queries (s : Wgmma.State) (answer : Bool) :
    (waitState s answer).base.scalar.core.queries = s.base.scalar.core.queries+1 := rfl
@[simp] theorem waitState_pending (s : Wgmma.State) (answer : Bool) :
    Wgmma.pending (waitState s answer).ledger = Wgmma.pending s.ledger := rfl
@[simp] theorem waitState_nat (s : Wgmma.State) (answer : Bool) (name : String) :
    lookup name (waitState s answer).base.scalar.core.thread.regs =
      if name = "%ready" then some (if answer then 1 else 0) else lookup name s.base.scalar.core.thread.regs := by
  exact Ampere.intAssign_nat _ _ _ _
@[simp] theorem testedState_status (s : Wgmma.State) (answer : Bool) :
    (testedState s answer).base.scalar.core.thread.status = s.base.scalar.core.thread.status := rfl
@[simp] theorem testedState_pc (s : Wgmma.State) (answer : Bool) :
    (testedState s answer).base.scalar.core.thread.pc = if answer then 57 else 55 := rfl
@[simp] theorem testedState_queries (s : Wgmma.State) (answer : Bool) :
    (testedState s answer).base.scalar.core.queries = s.base.scalar.core.queries+1 := rfl
@[simp] theorem testedState_pending (s : Wgmma.State) (answer : Bool) :
    Wgmma.pending (testedState s answer).ledger = Wgmma.pending s.ledger := rfl
@[simp] theorem testedState_nat (s : Wgmma.State) (answer : Bool) (name : String) :
    lookup name (testedState s answer).base.scalar.core.thread.regs =
      if name = "%ready" then some (if answer then 1 else 0) else lookup name s.base.scalar.core.thread.regs := by
  exact waitState_nat s answer name

theorem wait_test_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State) (bar parity : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 55)
    (hp : Wgmma.pending s.ledger = [])
    (hb : lookup "%waitbar" s.base.scalar.core.thread.regs = some bar)
    (hpar : lookup "%parity" s.base.scalar.core.thread.regs = some parity)
    (hbb : bar < 2^64) (hpb : parity < 2^32) :
    Wgmma.run ctx oracle code 2 s = .ok
      (testedState s (oracle.base.wait s.base.scalar.core.queries),
        [waitEvent ctx bar parity (oracle.base.wait s.base.scalar.core.queries)]) := by
  have hbmod : bar % 18446744073709551616 = bar := Nat.mod_eq_of_lt hbb
  have hpmod : parity % 4294967296 = parity := Nat.mod_eq_of_lt hpb
  have hfetch : code[s.base.scalar.core.thread.pc]? = some waitInstruction := by
    simp [hpc,code,Generated.hopper_double_buffer_gemm.program,waitInstruction]
  have hh := Hopper.try_wait_step (oracle := oracle.base) hr hfetch
    (show evalAddr ctx.id.tid.x s.base.scalar.core.thread ⟨.reg "%waitbar",0⟩ = .ok bar by
      simp [evalAddr,Ptx.eval,hb,wrap,hbmod,bind,Except.bind,pure,Except.pure])
    (show Ptx.eval ctx.id.tid.x s.base.scalar.core.thread (.reg "%parity") = .ok parity by simp [Ptx.eval,hpar])
  have h0 : Wgmma.step ctx oracle code s = .ok
      (waitState s (oracle.base.wait s.base.scalar.core.queries),
        [waitEvent ctx bar parity (oracle.base.wait s.base.scalar.core.queries)]) := by
    simpa [waitState,waitEvent,Wgmma.ordinaryState,wrap,hpmod] using
      Wgmma.ordinary_step hr hfetch (by intro wg he; cases he)
        (Wgmma.no_pending_names hp _) hh
  let s1 := waitState s (oracle.base.wait s.base.scalar.core.queries)
  have h1 : Wgmma.step ctx oracle code s1 = .ok
      (testedState s (oracle.base.wait s.base.scalar.core.queries),[]) := by
    have hs := Wgmma.branch_step (ctx := ctx) (oracle := oracle) (code := code)
      (s := s1) (value := if oracle.base.wait s.base.scalar.core.queries then 1 else 0) (name := "%ready") (positive := false) (target := 55)
      (by simp [s1,hr]) (by simp [s1,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1] using hp) (by simp [s1])
    cases ha : oracle.base.wait s.base.scalar.core.queries <;>
      simpa [s1,testedState,ha,hpc] using hs
  dsimp only [s1] at h1
  simp only [Wgmma.run,h0,h1,Except.bind,List.nil_append,List.append_nil]

def retryState : Nat → Wgmma.State → Wgmma.State
  | 0,s => s
  | n+1,s => testedState (retryState n s) false

@[simp] theorem retryState_status (n : Nat) (s : Wgmma.State) :
    (retryState n s).base.scalar.core.thread.status = s.base.scalar.core.thread.status := by
  induction n with
  | zero => rfl
  | succ n ih => simp [retryState,ih]
@[simp] theorem retryState_pc (n : Nat) (s : Wgmma.State) (hp : s.base.scalar.core.thread.pc = 55) :
    (retryState n s).base.scalar.core.thread.pc = 55 := by cases n <;> simp [retryState,hp]
@[simp] theorem retryState_queries (n : Nat) (s : Wgmma.State) :
    (retryState n s).base.scalar.core.queries = s.base.scalar.core.queries+n := by
  induction n with
  | zero => simp [retryState]
  | succ n ih => simp [retryState,ih,Nat.add_assoc]
@[simp] theorem retryState_pending (n : Nat) (s : Wgmma.State) :
    Wgmma.pending (retryState n s).ledger = Wgmma.pending s.ledger := by
  induction n with
  | zero => rfl
  | succ n ih => simp [retryState,ih]
theorem retryState_nat (n : Nat) (s : Wgmma.State) (name : String) (hn : name ≠ "%ready") :
    lookup name (retryState n s).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := by
  induction n with
  | zero => rfl
  | succ n ih => simp [retryState,hn,ih]

theorem arbitrary_failed_wait_prefix (ctx : Scalar.Context) (oracle : Wgmma.Oracle)
    (s : Wgmma.State) (bar parity n : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 55)
    (hp : Wgmma.pending s.ledger = [])
    (hb : lookup "%waitbar" s.base.scalar.core.thread.regs = some bar)
    (hpar : lookup "%parity" s.base.scalar.core.thread.regs = some parity)
    (hbb : bar < 2^64) (hpb : parity < 2^32)
    (hw : ∀ i < n, oracle.base.wait (s.base.scalar.core.queries+i) = false) :
    Wgmma.run ctx oracle code (2*n) s = .ok (retryState n s,List.replicate n (waitEvent ctx bar parity false)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hPrefix := ih (fun i hi => hw i (by omega))
    have next := wait_test_execute ctx oracle (retryState n s) bar parity
      (by simpa using hr) (retryState_pc n s hpc) (by simpa using hp)
      (by simpa [retryState_nat n s "%waitbar" (by decide)] using hb)
      (by simpa [retryState_nat n s "%parity" (by decide)] using hpar) hbb hpb
    rw [retryState_queries,hw n (by omega)] at next
    rw [show 2*(n+1) = 2*n+2 by omega,Wgmma.run_add,hPrefix]
    simpa [Except.bind,next,retryState,List.replicate_succ',List.append_assoc]

theorem testedState_float_frame (s : Wgmma.State) (answer : Bool) (name : String)
    (hx : name ≠ "%ready") (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (testedState s answer).base.scalar.floats = declarationLookup name s.base.scalar.floats := by
  simp only [testedState,waitState,Wgmma.integerPC,Wgmma.ordinaryState,Hopper.waitState,Ampere.intPC,Ampere.intAssign]
  simp [Scalar.intPC_float,Scalar.intAssign_float,hx,hn]

theorem retryState_float_frame (n : Nat) (s : Wgmma.State) (name : String)
    (hx : name ≠ "%ready") (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (retryState n s).base.scalar.floats = declarationLookup name s.base.scalar.floats := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [retryState,testedState_float_frame _ _ _ hx,ih]
    rw [retryState_nat n s name hx,hn]

end
end Ptx.Kernels.HopperDoubleBuffer
