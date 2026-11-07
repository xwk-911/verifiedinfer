import Ptx.Kernels.HopperDoubleBufferAccumulators

/-! One actual bounded K-loop iteration, PC 45 to its next loop/output entry.
The precondition describes registers and available accumulators, rather than
assuming an interpreter run. Failed waits are retained. Oracle value agreement,
source initialization and whole-launch memory/resource legality are separate.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def LoopRegisters (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) (mapA mapB : Nat) : Prop :=
  SelectionReady s tile ∧
  lookup "%tile" s.base.scalar.core.thread.regs = some tile ∧
  lookup "%tiles" s.base.scalar.core.thread.regs = some tiles ∧
  lookup "%leader" s.base.scalar.core.thread.regs = some (if leader then 1 else 0) ∧
  lookup "%mapa" s.base.scalar.core.thread.regs = some mapA ∧
  lookup "%mapb" s.base.scalar.core.thread.regs = some mapB

def preparedState (s : Wgmma.State) (tile tiles retries : Nat) (leader : Bool) : Wgmma.State :=
  preludeState (headerState s tile retries) tile tiles leader

def iterationState (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (tile tiles retries : Nat) (leader : Bool) (values : Fin 4 → ℝ) : Wgmma.State :=
  advanceState (computeState ctx oracle (preparedState s tile tiles retries leader)
    (aDescriptor (stage tile)) (bDescriptor (stage tile)) values) tile tiles

def iterationSteps (tile tiles retries : Nat) (leader : Bool) : Nat :=
  headerSteps tile retries+preludeSteps tile tiles leader+9

def iterationEvents (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (tile tiles retries : Nat) (leader : Bool) (mapA mapB : Nat) (values : Fin 4 → ℝ) : List Wgmma.Event :=
  (List.replicate retries (waitEvent ctx (barrierAddress (stage tile)) (expectedParity tile) false)++
    [waitEvent ctx (barrierAddress (stage tile)) (expectedParity tile) true])++
  preludeEvents ctx oracle (headerState s tile retries) tile tiles leader mapA mapB++
  (computeEvents ctx oracle (preparedState s tile tiles retries leader) (aDescriptor (stage tile)) (bDescriptor (stage tile)) values++
    advanceEvents (computeState ctx oracle (preparedState s tile tiles retries leader) (aDescriptor (stage tile)) (bDescriptor (stage tile)) values))

theorem headerState_selected_nat (s : Wgmma.State) (tile retries : Nat) (name : String)
    (hn : name ∉ ["%phase0","%phase1","%ready"]) :
    lookup name (headerState s tile retries).base.scalar.core.thread.regs =
      lookup name (selectionState s tile).base.scalar.core.thread.regs := by
  have hh : name ≠ "%phase0" ∧ name ≠ "%phase1" ∧ name ≠ "%ready" := by simpa using hn
  rw [headerState,phaseState_nat_frame _ _ _ hh.1 hh.2.1,testedState_nat]
  simp only [hh.2.2,ite_false]
  rw [retryState_nat _ _ _ hh.2.2]

theorem preparedState_bookkeeping (s : Wgmma.State) (tile tiles retries : Nat) (leader : Bool) :
    bookkeeping (preparedState s tile tiles retries leader) = bookkeeping s :=
  (prelude_preserves_bookkeeping _ tile tiles leader).trans (header_preserves_bookkeeping s tile retries)

@[simp] theorem preparedState_pending (s : Wgmma.State) (tile tiles retries : Nat) (leader : Bool) :
    Wgmma.pending (preparedState s tile tiles retries leader).ledger = Wgmma.pending s.ledger := by simp [preparedState]
@[simp] theorem preparedState_queries (s : Wgmma.State) (tile tiles retries : Nat) (leader : Bool) :
    (preparedState s tile tiles retries leader).base.scalar.core.queries =
      s.base.scalar.core.queries+retries+1+(if needsPrefetch tile tiles leader then 4 else 0) := by simp [preparedState]

theorem iteration_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (tile tiles retries : Nat) (leader : Bool) (mapA mapB : Nat) (values : Fin 4 → ℝ)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s tile tiles leader mapA mapB) (hacc : Accumulators s values)
    (hlt : tile < tiles) (hbound : tiles ≤ 2^28)
    (hfalse : ∀ i < retries, oracle.base.wait (s.base.scalar.core.queries+i) = false)
    (htrue : oracle.base.wait (s.base.scalar.core.queries+retries) = true)
    (hshape : needsPrefetch tile tiles leader →
      (oracle.base.tmaBytes (s.base.scalar.core.queries+retries+2)).length =
        (oracle.base.descriptor (s.base.scalar.core.queries+retries+1)).bytes ∧
      (oracle.base.tmaBytes (s.base.scalar.core.queries+retries+4)).length =
        (oracle.base.descriptor (s.base.scalar.core.queries+retries+3)).bytes) :
    Wgmma.run ctx oracle code (iterationSteps tile tiles retries leader) s = .ok
      (iterationState ctx oracle s tile tiles retries leader values,
        iterationEvents ctx oracle s tile tiles retries leader mapA mapB values) := by
  obtain ⟨hsel,ht,hT,hl,hma,hmb⟩ := hregs
  have hhead := header_execute ctx oracle s tile retries hr hpc hp hsel hfalse htrue
  have hguard := prelude_execute ctx oracle (headerState s tile retries) tile tiles leader mapA mapB
    (by simpa using hr) (headerState_pc s tile retries) (by simpa using hp)
    (by rwa [headerState_nat_frame _ _ _ "%tile" (by decide)])
    (by rwa [headerState_nat_frame _ _ _ "%tiles" (by decide)])
    (by rwa [headerState_nat_frame _ _ _ "%leader" (by decide)])
    (by rw [headerState_selected_nat _ _ _ "%even" (by decide)]; exact selectionState_even s tile)
    (by rw [headerState_nat_frame _ _ _ "%bar0" (by decide)]; exact hsel ("%bar0",0) (by simp [selectionBindings]))
    (by rw [headerState_nat_frame _ _ _ "%bar1" (by decide)]; exact hsel ("%bar1",8) (by simp [selectionBindings]))
    (by rwa [headerState_nat_frame _ _ _ "%mapa" (by decide)])
    (by rwa [headerState_nat_frame _ _ _ "%mapb" (by decide)]) hlt hbound
    (by simpa [Nat.add_assoc] using hshape)
  have hprepared : Accumulators (preparedState s tile tiles retries leader) values :=
    prelude_preserves_accumulators _ tile tiles leader values (header_preserves_accumulators s tile retries values hacc)
  have hpg : (preparedState s tile tiles retries leader).ledger.groups = s.ledger.groups :=
    congrArg Prod.fst (preparedState_bookkeeping s tile tiles retries leader)
  have hpcmp : (preparedState s tile tiles retries leader).ledger.completed = s.ledger.completed :=
    congrArg (fun x => x.2.1) (preparedState_bookkeeping s tile tiles retries leader)
  have hpc' : (preparedState s tile tiles retries leader).ledger.completed ≤ (preparedState s tile tiles retries leader).ledger.groups := by
    rwa [hpg,hpcmp]
  have hpp : Wgmma.pending (preparedState s tile tiles retries leader).ledger = [] := by simpa using hp
  obtain ⟨_,hA,hB,_⟩ := selectionState_operands s tile
  have hpa : lookup "%ad" (preparedState s tile tiles retries leader).base.scalar.core.thread.regs = some (aDescriptor (stage tile)) := by
    rw [preparedState,preludeState_nat_frame _ _ _ _ "%ad" (by decide),headerState_selected_nat _ _ _ "%ad" (by decide)]
    exact hA
  have hpb : lookup "%bd" (preparedState s tile tiles retries leader).base.scalar.core.thread.regs = some (bDescriptor (stage tile)) := by
    rw [preparedState,preludeState_nat_frame _ _ _ _ "%bd" (by decide),headerState_selected_nat _ _ _ "%bd" (by decide)]
    exact hB
  have hn := compute_and_advance_execute ctx oracle (preparedState s tile tiles retries leader)
    (aDescriptor (stage tile)) (bDescriptor (stage tile)) values tile tiles
    (by simpa [preparedState] using hr) (by simp [preparedState]) hpa hpb
    (source_reads_accumulators _ values hpp hprepared) hpc' hpp
    (by rw [preparedState,preludeState_nat_frame _ _ _ _ "%slot" (by decide),headerState_nat_frame _ _ _ "%slot" (by decide)]; exact hsel ("%slot",tile%2) (by simp [selectionBindings]))
    (by rwa [preparedState,preludeState_nat_frame _ _ _ _ "%tile" (by decide),headerState_nat_frame _ _ _ "%tile" (by decide)])
    (by rwa [preparedState,preludeState_nat_frame _ _ _ _ "%tiles" (by decide),headerState_nat_frame _ _ _ "%tiles" (by decide)]) hlt (by omega)
  dsimp only [preparedState] at hn
  rw [iterationSteps,Wgmma.run_add,Wgmma.run_add,hhead]
  simp only [Except.bind,hguard,hn,List.append_assoc,iterationState,iterationEvents,preparedState]

@[simp] theorem iterationState_pc (ctx oracle s tile tiles retries leader values) :
    (iterationState ctx oracle s tile tiles retries leader values).base.scalar.core.thread.pc =
      if tile+1 < tiles then 45 else 85 := rfl
@[simp] theorem iterationState_queries (ctx oracle s tile tiles retries leader values) :
    (iterationState ctx oracle s tile tiles retries leader values).base.scalar.core.queries =
      s.base.scalar.core.queries+retries+1+(if needsPrefetch tile tiles leader then 4 else 0)+2 := by
  simp [iterationState]

theorem iterationState_pending (ctx oracle s tile tiles retries leader values)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups) :
    Wgmma.pending (iterationState ctx oracle s tile tiles retries leader values).ledger = [] := by
  have hpg := congrArg Prod.fst (preparedState_bookkeeping s tile tiles retries leader)
  have hpcmp := congrArg (fun x => x.2.1) (preparedState_bookkeeping s tile tiles retries leader)
  simp only [bookkeeping] at hpg hpcmp
  rw [iterationState,advanceState_pending]
  apply computeState_no_pending
  · rwa [hpg,hpcmp]
  · simpa using hp

@[simp] theorem preparedState_groups (s : Wgmma.State) (tile tiles retries : Nat) (leader : Bool) :
    (preparedState s tile tiles retries leader).ledger.groups = s.ledger.groups :=
  congrArg Prod.fst (preparedState_bookkeeping s tile tiles retries leader)
@[simp] theorem preparedState_completed (s : Wgmma.State) (tile tiles retries : Nat) (leader : Bool) :
    (preparedState s tile tiles retries leader).ledger.completed = s.ledger.completed :=
  congrArg (fun x => x.2.1) (preparedState_bookkeeping s tile tiles retries leader)

theorem iterationState_control_frame (ctx oracle s tile tiles retries leader values)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups) (name : String)
    (hn : name ∉ ["%phase0","%phase1","%even","%waitbar","%ad","%bd","%parity","%ready",
      "%next","%more","%nextbar","%copya","%copyb","%ay","%slot","%tile","%d0","%d1","%d2","%d3"]) :
    lookup name (iterationState ctx oracle s tile tiles retries leader values).base.scalar.core.thread.regs =
      lookup name s.base.scalar.core.thread.regs := by
  have hH : name ∉ ["%even","%waitbar","%ad","%bd","%parity","%ready","%phase0","%phase1"] := by simp_all
  have hP : name ∉ ["%next","%more","%nextbar","%copya","%copyb","%ay"] := by simp_all
  have hC : name ∉ ["%d0","%d1","%d2","%d3"] := by simp_all
  have hT : name ∉ ["%slot","%tile","%more"] := by simp_all
  rw [iterationState,advanceState_nat_frame _ _ _ _ hT,
    computeState_nat_frame _ _ _ _ _ _ (by simpa using hc) (by simpa using hp) _ hC,
    preparedState,preludeState_nat_frame _ _ _ _ _ hP,headerState_nat_frame _ _ _ _ hH]

theorem iterationState_phases (ctx oracle s tile tiles retries leader values)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hsel : SelectionReady s tile) :
    lookup "%phase0" (iterationState ctx oracle s tile tiles retries leader values).base.scalar.core.thread.regs = some (phaseZero (tile+1)) ∧
    lookup "%phase1" (iterationState ctx oracle s tile tiles retries leader values).base.scalar.core.thread.regs = some (phaseOne (tile+1)) := by
  have hphase := headerState_phases s tile retries hsel
  constructor
  · rw [iterationState,advanceState_nat_frame _ _ _ "%phase0" (by decide),
      computeState_nat_frame _ _ _ _ _ _ (by simpa using hc) (by simpa using hp) "%phase0" (by decide),
      preparedState,preludeState_nat_frame _ _ _ _ "%phase0" (by decide)]
    exact hphase.1
  · rw [iterationState,advanceState_nat_frame _ _ _ "%phase1" (by decide),
      computeState_nat_frame _ _ _ _ _ _ (by simpa using hc) (by simpa using hp) "%phase1" (by decide),
      preparedState,preludeState_nat_frame _ _ _ _ "%phase1" (by decide)]
    exact hphase.2

theorem iterationState_registers (ctx oracle s tile tiles retries leader values mapA mapB)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s tile tiles leader mapA mapB) :
    LoopRegisters (iterationState ctx oracle s tile tiles retries leader values) (tile+1) tiles leader mapA mapB := by
  obtain ⟨hsel,ht,hT,hl,hma,hmb⟩ := hregs
  have hcounter := advanceState_counters
    (computeState ctx oracle (preparedState s tile tiles retries leader) (aDescriptor (stage tile)) (bDescriptor (stage tile)) values) tile tiles
  have hphase := iterationState_phases ctx oracle s tile tiles retries leader values hp hc hsel
  refine ⟨?_,hcounter.1,?_,?_,?_,?_⟩
  · intro binding hm
    simp only [selectionBindings,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcounter.2
    · rw [iterationState_control_frame _ _ _ _ _ _ _ _ hp hc "%bar0" (by decide)]
      exact hsel ("%bar0",0) (by simp [selectionBindings])
    · rw [iterationState_control_frame _ _ _ _ _ _ _ _ hp hc "%bar1" (by decide)]
      exact hsel ("%bar1",8) (by simp [selectionBindings])
    · rw [iterationState_control_frame _ _ _ _ _ _ _ _ hp hc "%ad0" (by decide)]
      exact hsel ("%ad0",68720001025) (by simp [selectionBindings])
    · rw [iterationState_control_frame _ _ _ _ _ _ _ _ hp hc "%bd0" (by decide)]
      exact hsel ("%bd0",68720001153) (by simp [selectionBindings])
    · rw [iterationState_control_frame _ _ _ _ _ _ _ _ hp hc "%ad1" (by decide)]
      exact hsel ("%ad1",68720001169) (by simp [selectionBindings])
    · rw [iterationState_control_frame _ _ _ _ _ _ _ _ hp hc "%bd1" (by decide)]
      exact hsel ("%bd1",68720001297) (by simp [selectionBindings])
    · exact hphase.1
    · exact hphase.2
  · rwa [iterationState_control_frame _ _ _ _ _ _ _ _ hp hc "%tiles" (by decide)]
  · rwa [iterationState_control_frame _ _ _ _ _ _ _ _ hp hc "%leader" (by decide)]
  · rwa [iterationState_control_frame _ _ _ _ _ _ _ _ hp hc "%mapa" (by decide)]
  · rwa [iterationState_control_frame _ _ _ _ _ _ _ _ hp hc "%mapb" (by decide)]

theorem iterationState_accumulators (ctx oracle s tile tiles retries leader values)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups) :
    Accumulators (iterationState ctx oracle s tile tiles retries leader values)
      (oracle.matrix (preparedState s tile tiles retries leader).base.scalar.core.queries) := by
  intro i
  have hn := computeState_accumulators ctx oracle (preparedState s tile tiles retries leader)
    (aDescriptor (stage tile)) (bDescriptor (stage tile)) values (by simpa using hc) (by simpa using hp) i
  have hx : computeSlotName i ∉ ["%slot","%tile","%more"] := by fin_cases i <;> decide
  constructor
  · rw [iterationState,advanceState_float_frame _ _ _ _ hx hn.2]
    exact hn.1
  · rw [iterationState,advanceState_nat_frame _ _ _ _ hx]
    exact hn.2

theorem iterationState_status (ctx oracle s tile tiles retries leader values)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups) :
    (iterationState ctx oracle s tile tiles retries leader values).base.scalar.core.thread.status = s.base.scalar.core.thread.status := by
  rw [iterationState,advanceState_status,computeState_status _ _ _ _ _ _ (by simpa using hc) (by simpa using hp)]
  simp [preparedState]

theorem iterationState_groups (ctx oracle s tile tiles retries leader values) :
    (iterationState ctx oracle s tile tiles retries leader values).ledger.groups = s.ledger.groups+1 := by
  change (computeState ctx oracle (preparedState s tile tiles retries leader)
    (aDescriptor (stage tile)) (bDescriptor (stage tile)) values).ledger.groups = _
  simp

theorem iterationState_completed (ctx oracle s tile tiles retries leader values)
    (hc : s.ledger.completed ≤ s.ledger.groups) :
    (iterationState ctx oracle s tile tiles retries leader values).ledger.completed = s.ledger.groups+1 := by
  change (computeState ctx oracle (preparedState s tile tiles retries leader)
    (aDescriptor (stage tile)) (bDescriptor (stage tile)) values).ledger.completed = _
  rw [computeState_completed _ _ _ _ _ _ (by simpa using hc),preparedState_groups]

end
end Ptx.Kernels.HopperDoubleBuffer
