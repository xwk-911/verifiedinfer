import Ptx.Kernels.HopperDoubleBufferPrelude

/-! Register availability for the real loop, not arithmetic oracle correctness.
The preceding source segments preserve all four values with no integer shadow;
source MMA therefore consumes these values without an assumed execute result.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def Accumulators (s : Wgmma.State) (values : Fin 4 → ℝ) : Prop :=
  ∀ i, declarationLookup (computeSlotName i) s.base.scalar.floats = some (.f32,values i) ∧
    lookup (computeSlotName i) s.base.scalar.core.thread.regs = none

theorem header_preserves_accumulators (s : Wgmma.State) (tile retries : Nat) (values : Fin 4 → ℝ)
    (hv : Accumulators s values) : Accumulators (headerState s tile retries) values := by
  intro i
  have hx : computeSlotName i ∉ ["%even","%waitbar","%ad","%bd","%parity","%ready","%phase0","%phase1"] := by
    fin_cases i <;> decide
  constructor
  · rw [headerState_float_frame _ _ _ _ hx (hv i).2]
    exact (hv i).1
  · rw [headerState_nat_frame _ _ _ _ hx]
    exact (hv i).2

theorem prelude_preserves_accumulators (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) (values : Fin 4 → ℝ)
    (hv : Accumulators s values) : Accumulators (preludeState s tile tiles leader) values := by
  intro i
  have hx : computeSlotName i ∉ ["%next","%more","%nextbar","%copya","%copyb","%ay"] := by
    fin_cases i <;> decide
  constructor
  · rw [preludeState_float_frame _ _ _ _ _ hx (hv i).2]
    exact (hv i).1
  · rw [preludeState_nat_frame _ _ _ _ _ hx]
    exact (hv i).2

theorem source_reads_accumulators (s : Wgmma.State) (values : Fin 4 → ℝ)
    (hp : Wgmma.pending s.ledger = []) (hv : Accumulators s values) :
    Wgmma.readScaledAccumulator (computeFence s) ⟨"%d0","%d1","%d2","%d3"⟩ 1 = .ok values := by
  have hp' : Wgmma.pending (computeFence s).ledger = [] := hp
  have hvalue (name : String) : Wgmma.pendingValue (computeFence s).ledger name = none := by
    unfold Wgmma.pendingValue
    rw [hp']
    rfl
  have he (i : Fin 4) : Wgmma.evalAccumulator (computeFence s) (computeSlotName i) = .ok (values i) := by
    unfold Wgmma.evalAccumulator
    rw [hvalue]
    change Wgmma.liftScalar (Scalar.eval .f32 s.base.scalar (.reg (computeSlotName i))) = _
    simp [Scalar.eval,Scalar.require,(hv i).1,Wgmma.liftScalar,bind,Except.bind,pure,Except.pure]
  have h0 : Wgmma.evalAccumulator (computeFence s) "%d0" = .ok (values 0) := he 0
  have h1 : Wgmma.evalAccumulator (computeFence s) "%d1" = .ok (values 1) := he 1
  have h2 : Wgmma.evalAccumulator (computeFence s) "%d2" = .ok (values 2) := he 2
  have h3 : Wgmma.evalAccumulator (computeFence s) "%d3" = .ok (values 3) := he 3
  simp [Wgmma.readScaledAccumulator,Wgmma.readAccumulator,h0,h1,h2,h3,bind,Except.bind,pure,Except.pure]
  funext i
  fin_cases i <;> rfl

def bookkeeping (s : Wgmma.State) := (s.ledger.groups,s.ledger.completed,s.ledger.calls,s.ledger.syncs)

@[simp] theorem integerAssign_bookkeeping (s : Wgmma.State) (i : Ptx.Instr) (dst : String) (value : Nat) :
    bookkeeping (Wgmma.integerAssign s i dst value) = bookkeeping s := rfl
@[simp] theorem integerPC_bookkeeping (s : Wgmma.State) (i : Ptx.Instr) (pc : Nat) :
    bookkeeping (Wgmma.integerPC s i pc) = bookkeeping s := rfl
@[simp] theorem advanceOrdinary_bookkeeping (s : Wgmma.State) (i : Hopper.Instr) :
    bookkeeping (Wgmma.advanceOrdinary s i) = bookkeeping s := rfl
@[simp] theorem tmaState_bookkeeping (s : Wgmma.State) (i : Hopper.Instr) :
    bookkeeping (Wgmma.tmaState s i) = bookkeeping s := rfl
@[simp] theorem testedState_bookkeeping (s : Wgmma.State) (answer : Bool) :
    bookkeeping (testedState s answer) = bookkeeping s := rfl
@[simp] theorem retryState_bookkeeping (s : Wgmma.State) (n : Nat) :
    bookkeeping (retryState n s) = bookkeeping s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [retryState,testedState_bookkeeping,ih]
@[simp] theorem selectionState_bookkeeping (s : Wgmma.State) (tile : Nat) :
    bookkeeping (selectionState s tile) = bookkeeping s := by
  by_cases h : tile%2 = 0 <;> simp only [selectionState,selectionPrefix,h,ite_true,ite_false,integerAssign_bookkeeping,integerPC_bookkeeping]
@[simp] theorem phaseState_bookkeeping (s : Wgmma.State) (tile : Nat) :
    bookkeeping (phaseState s tile) = bookkeeping s := by
  by_cases h : tile%2 = 0 <;> simp only [phaseState,h,ite_true,ite_false,integerAssign_bookkeeping,integerPC_bookkeeping]

theorem header_preserves_bookkeeping (s : Wgmma.State) (tile retries : Nat) :
    bookkeeping (headerState s tile retries) = bookkeeping s := by
  simp only [headerState,phaseState_bookkeeping,testedState_bookkeeping,retryState_bookkeeping,selectionState_bookkeeping]

theorem prelude_preserves_bookkeeping (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) :
    bookkeeping (preludeState s tile tiles leader) = bookkeeping s := by
  by_cases hp : needsPrefetch tile tiles leader <;> by_cases he : tile%2 = 0 <;> by_cases ht : tile+1 < tiles
  all_goals simp only [preludeState,prefetchState,prefetchTransferState,prefetchAIssued,prefetchArrived,
    prefetchAddressState,prefetchSelected,prefetchAddressPrefix,prefetchGuardState,prefetchGuardPrefix,hp,he,ht,ite_true,ite_false,
    integerAssign_bookkeeping,integerPC_bookkeeping,advanceOrdinary_bookkeeping,tmaState_bookkeeping]

end
end Ptx.Kernels.HopperDoubleBuffer
