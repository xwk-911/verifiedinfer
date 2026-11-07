import Ptx.Kernels.HopperDoubleBufferSelection

/-! The actual source loop header, PC 45 to PC 61, with arbitrary tile index,
all lane contexts, arbitrary retained matrix values and any finite failed-wait
prefix. Only this header's oracle answers are prescribed. It is not a full
iteration, initial-state reconstruction or admitted launch theorem. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def headerState (s : Wgmma.State) (tile retries : Nat) : Wgmma.State :=
  phaseState (testedState (retryState retries (selectionState s tile)) true) tile
def headerSteps (tile retries : Nat) : Nat := selectionSteps tile+2*retries+2+phaseSteps tile

theorem header_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle)
    (s : Wgmma.State) (tile retries : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hregs : SelectionReady s tile)
    (hfalse : ∀ i < retries, oracle.base.wait (s.base.scalar.core.queries+i) = false)
    (htrue : oracle.base.wait (s.base.scalar.core.queries+retries) = true) :
    Wgmma.run ctx oracle code (headerSteps tile retries) s = .ok
      (headerState s tile retries,
        List.replicate retries (waitEvent ctx (barrierAddress (stage tile)) (expectedParity tile) false)++
          [waitEvent ctx (barrierAddress (stage tile)) (expectedParity tile) true]) := by
  let selected := selectionState s tile
  let retried := retryState retries selected
  let tested := testedState retried true
  have hselected := selection_execute ctx oracle s tile hr hpc hp hregs
  obtain ⟨hbar,ha,hb,hpar⟩ := selectionState_operands s tile
  have hbarBound : barrierAddress (stage tile) < 2^64 := by
    have hs := (stage tile).isLt
    dsimp [barrierAddress]
    omega
  have hparBound : expectedParity tile < 2^32 := by have := expected_parity_bounded tile; omega
  have hfailed := arbitrary_failed_wait_prefix ctx oracle selected
    (barrierAddress (stage tile)) (expectedParity tile) retries
    (by simpa [selected] using hr) (by simp [selected]) (by simpa [selected] using hp)
    hbar hpar hbarBound hparBound (by simpa [selected] using hfalse)
  have hsucceeded := wait_test_execute ctx oracle retried (barrierAddress (stage tile)) (expectedParity tile)
    (by simpa [retried,selected] using hr) (retryState_pc retries selected (by simp [selected]))
    (by simpa [retried,selected] using hp)
    (by simpa [retried,retryState_nat retries selected "%waitbar" (by decide)] using hbar)
    (by simpa [retried,retryState_nat retries selected "%parity" (by decide)] using hpar) hbarBound hparBound
  have hq : oracle.base.wait retried.base.scalar.core.queries = true := by
    simpa [retried,selected] using htrue
  rw [hq] at hsucceeded
  have heven : lookup "%even" tested.base.scalar.core.thread.regs = some (if tile%2 = 0 then 1 else 0) := by
    simp only [tested,testedState_nat]
    simp only [show ("%even" : String) ≠ "%ready" from by decide,ite_false]
    rw [retryState_nat retries selected "%even" (by decide)]
    exact selectionState_even s tile
  have hzero : lookup "%phase0" tested.base.scalar.core.thread.regs = some (phaseZero tile) := by
    simp only [tested,testedState_nat]
    simp only [show ("%phase0" : String) ≠ "%ready" from by decide,ite_false]
    rw [retryState_nat retries selected "%phase0" (by decide),selectionState_nat_frame s tile "%phase0" (by decide)]
    exact hregs ("%phase0",phaseZero tile) (by simp [selectionBindings])
  have hone : lookup "%phase1" tested.base.scalar.core.thread.regs = some (phaseOne tile) := by
    simp only [tested,testedState_nat]
    simp only [show ("%phase1" : String) ≠ "%ready" from by decide,ite_false]
    rw [retryState_nat retries selected "%phase1" (by decide),selectionState_nat_frame s tile "%phase1" (by decide)]
    exact hregs ("%phase1",phaseOne tile) (by simp [selectionBindings])
  have hphase := phase_update_execute ctx oracle tested tile (by simpa [tested,retried,selected] using hr)
    (by simp [tested]) (by simpa [tested,retried,selected] using hp) heven hzero hone
  rw [headerSteps,Wgmma.run_add,Wgmma.run_add,Wgmma.run_add,hselected]
  dsimp only [selected,retried,tested] at hfailed hsucceeded hphase
  simp only [Except.bind,hfailed,hsucceeded,hphase,List.nil_append,List.append_nil,headerState]

@[simp] theorem headerState_pc (s : Wgmma.State) (tile retries : Nat) :
    (headerState s tile retries).base.scalar.core.thread.pc = 61 := by simp [headerState]
@[simp] theorem headerState_status (s : Wgmma.State) (tile retries : Nat) :
    (headerState s tile retries).base.scalar.core.thread.status = s.base.scalar.core.thread.status := by simp [headerState]
@[simp] theorem headerState_queries (s : Wgmma.State) (tile retries : Nat) :
    (headerState s tile retries).base.scalar.core.queries = s.base.scalar.core.queries+retries+1 := by simp [headerState]
@[simp] theorem headerState_pending (s : Wgmma.State) (tile retries : Nat) :
    Wgmma.pending (headerState s tile retries).ledger = Wgmma.pending s.ledger := by simp [headerState]

theorem headerState_nat_frame (s : Wgmma.State) (tile retries : Nat) (name : String)
    (hn : name ∉ ["%even","%waitbar","%ad","%bd","%parity","%ready","%phase0","%phase1"]) :
    lookup name (headerState s tile retries).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := by
  have hh : name ≠ "%even" ∧ name ≠ "%waitbar" ∧ name ≠ "%ad" ∧ name ≠ "%bd" ∧ name ≠ "%parity" ∧
      name ≠ "%ready" ∧ name ≠ "%phase0" ∧ name ≠ "%phase1" := by simpa using hn
  rw [headerState,phaseState_nat_frame _ _ _ hh.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2,testedState_nat]
  simp only [hh.2.2.2.2.2.1,ite_false]
  rw [retryState_nat _ _ _ hh.2.2.2.2.2.1,selectionState_nat_frame]
  simp [hh]

theorem headerState_float_frame (s : Wgmma.State) (tile retries : Nat) (name : String)
    (hx : name ∉ ["%even","%waitbar","%ad","%bd","%parity","%ready","%phase0","%phase1"])
    (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (headerState s tile retries).base.scalar.floats = declarationLookup name s.base.scalar.floats := by
  have hh : name ≠ "%even" ∧ name ≠ "%waitbar" ∧ name ≠ "%ad" ∧ name ≠ "%bd" ∧ name ≠ "%parity" ∧
      name ≠ "%ready" ∧ name ≠ "%phase0" ∧ name ≠ "%phase1" := by simpa using hx
  have hselect : name ∉ ["%even","%waitbar","%ad","%bd","%parity"] := by simp [hh]
  have hs : lookup name (selectionState s tile).base.scalar.core.thread.regs = none := by
    rw [selectionState_nat_frame _ _ _ hselect,hn]
  have hr : lookup name (retryState retries (selectionState s tile)).base.scalar.core.thread.regs = none := by
    rw [retryState_nat _ _ _ hh.2.2.2.2.2.1,hs]
  rw [headerState,phaseState_float_frame _ _ _ hh.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2,
    testedState_float_frame _ _ _ hh.2.2.2.2.2.1 hr,
    retryState_float_frame _ _ _ hh.2.2.2.2.2.1 hs,
    selectionState_float_frame _ _ _ hselect hn]
  simp [hr,hh.2.2.2.2.2.1]

theorem headerState_phases (s : Wgmma.State) (tile retries : Nat) (hregs : SelectionReady s tile) :
    lookup "%phase0" (headerState s tile retries).base.scalar.core.thread.regs = some (phaseZero (tile+1)) ∧
    lookup "%phase1" (headerState s tile retries).base.scalar.core.thread.regs = some (phaseOne (tile+1)) := by
  apply phaseState_phases
  · simp only [testedState_nat]
    simp only [show ("%phase0" : String) ≠ "%ready" from by decide,ite_false]
    rw [retryState_nat _ _ _ (by decide),selectionState_nat_frame _ _ _ (by decide)]
    exact hregs ("%phase0",phaseZero tile) (by simp [selectionBindings])
  · simp only [testedState_nat]
    simp only [show ("%phase1" : String) ≠ "%ready" from by decide,ite_false]
    rw [retryState_nat _ _ _ (by decide),selectionState_nat_frame _ _ _ (by decide)]
    exact hregs ("%phase1",phaseOne tile) (by simp [selectionBindings])

end
end Ptx.Kernels.HopperDoubleBuffer
