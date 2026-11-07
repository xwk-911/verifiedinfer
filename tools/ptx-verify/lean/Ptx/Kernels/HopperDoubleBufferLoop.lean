import Ptx.Kernels.HopperDoubleBufferIteration

/-! Arbitrary finite source-loop composition with a retry count per tile.
Reply conditions are indexed by a query schedule defined independently of
interpreter runs. The initial loop invariant is explicit; initial kernel
reconstruction, output, and whole-launch admission remain separate. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev LoopCheckpoint := Wgmma.State × (Fin 4 → ℝ)

def loopCheckpoint (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (first tiles : Nat)
    (leader : Bool) (retries : Nat → Nat) (s : Wgmma.State) (values : Fin 4 → ℝ) : Nat → LoopCheckpoint
  | 0 => (s,values)
  | n+1 =>
    let old := loopCheckpoint ctx oracle first tiles leader retries s values n
    let tile := first+n
    (iterationState ctx oracle old.1 tile tiles (retries tile) leader old.2,
     oracle.matrix (preparedState old.1 tile tiles (retries tile) leader).base.scalar.core.queries)

def loopQuery (first tiles : Nat) (leader : Bool) (retries : Nat → Nat) (query : Nat) : Nat → Nat
  | 0 => query
  | n+1 => loopQuery first tiles leader retries query n+retries (first+n)+1+
      (if needsPrefetch (first+n) tiles leader then 4 else 0)+2

def loopFuel (first tiles : Nat) (leader : Bool) (retries : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => loopFuel first tiles leader retries n+iterationSteps (first+n) tiles (retries (first+n)) leader

def loopEvents (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (first tiles : Nat)
    (leader : Bool) (retries : Nat → Nat) (s : Wgmma.State) (values : Fin 4 → ℝ) (mapA mapB : Nat) : Nat → List Wgmma.Event
  | 0 => []
  | n+1 =>
    let old := loopCheckpoint ctx oracle first tiles leader retries s values n
    loopEvents ctx oracle first tiles leader retries s values mapA mapB n++
      iterationEvents ctx oracle old.1 (first+n) tiles (retries (first+n)) leader mapA mapB old.2

def LoopReplies (oracle : Wgmma.Oracle) (query tile tiles retry : Nat) (leader : Bool) : Prop :=
  (∀ i < retry, oracle.base.wait (query+i) = false) ∧
  oracle.base.wait (query+retry) = true ∧
  (needsPrefetch tile tiles leader →
    (oracle.base.tmaBytes (query+retry+2)).length = (oracle.base.descriptor (query+retry+1)).bytes ∧
    (oracle.base.tmaBytes (query+retry+4)).length = (oracle.base.descriptor (query+retry+3)).bytes)

def CheckpointReady (cp : LoopCheckpoint) (tile tiles : Nat) (leader : Bool) (mapA mapB : Nat) : Prop :=
  cp.1.base.scalar.core.thread.status = .running ∧
  cp.1.base.scalar.core.thread.pc = (if tile < tiles then 45 else 85) ∧
  Wgmma.pending cp.1.ledger = [] ∧ cp.1.ledger.completed ≤ cp.1.ledger.groups ∧
  LoopRegisters cp.1 tile tiles leader mapA mapB ∧ Accumulators cp.1 cp.2

@[simp] theorem loopCheckpoint_queries (ctx oracle first tiles leader retries s values n) :
    (loopCheckpoint ctx oracle first tiles leader retries s values n).1.base.scalar.core.queries =
      loopQuery first tiles leader retries s.base.scalar.core.queries n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [loopCheckpoint,iterationState_queries,ih,loopQuery]

@[simp] theorem loopCheckpoint_groups (ctx oracle first tiles leader retries s values n) :
    (loopCheckpoint ctx oracle first tiles leader retries s values n).1.ledger.groups = s.ledger.groups+n := by
  induction n with
  | zero => simp [loopCheckpoint]
  | succ n ih => simp only [loopCheckpoint,iterationState_groups,ih,Nat.add_succ]

theorem loopCheckpoint_ready (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (first tiles : Nat)
    (leader : Bool) (retries : Nat → Nat) (s : Wgmma.State) (values : Fin 4 → ℝ) (mapA mapB : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s first tiles leader mapA mapB) (hacc : Accumulators s values)
    (hfirst : first < tiles) (n : Nat) (hcount : first+n ≤ tiles) :
    CheckpointReady (loopCheckpoint ctx oracle first tiles leader retries s values n) (first+n) tiles leader mapA mapB := by
  induction n with
  | zero => simpa [CheckpointReady,loopCheckpoint,hfirst] using And.intro hr (And.intro hpc (And.intro hp (And.intro hc (And.intro hregs hacc))))
  | succ n ih =>
    have hold := ih (by omega)
    obtain ⟨hr',hpc',hp',hc',hregs',hacc'⟩ := hold
    let old := loopCheckpoint ctx oracle first tiles leader retries s values n
    have hnext := iterationState_registers ctx oracle old.1 (first+n) tiles (retries (first+n)) leader old.2 mapA mapB hp' hc' hregs'
    have hnewAcc := iterationState_accumulators ctx oracle old.1 (first+n) tiles (retries (first+n)) leader old.2 hp' hc'
    have hnewPending := iterationState_pending ctx oracle old.1 (first+n) tiles (retries (first+n)) leader old.2 hp' hc'
    have hnewStatus := iterationState_status ctx oracle old.1 (first+n) tiles (retries (first+n)) leader old.2 hp' hc'
    refine ⟨?_,?_,hnewPending,?_,?_,hnewAcc⟩
    · simpa only [loopCheckpoint] using hnewStatus.trans hr'
    · simp only [loopCheckpoint,iterationState_pc,Nat.add_succ]
    · change (iterationState ctx oracle old.1 (first+n) tiles (retries (first+n)) leader old.2).ledger.completed ≤
        (iterationState ctx oracle old.1 (first+n) tiles (retries (first+n)) leader old.2).ledger.groups
      rw [iterationState_completed _ _ _ _ _ _ _ _ hc',iterationState_groups]
    · simpa only [loopCheckpoint,Nat.add_succ] using hnext

theorem loop_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (first tiles : Nat)
    (leader : Bool) (retries : Nat → Nat) (s : Wgmma.State) (values : Fin 4 → ℝ) (mapA mapB : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s first tiles leader mapA mapB) (hacc : Accumulators s values)
    (hfirst : first < tiles) (hbound : tiles ≤ 2^28) (n : Nat) (hcount : first+n ≤ tiles)
    (hreplies : ∀ i < n, LoopReplies oracle (loopQuery first tiles leader retries s.base.scalar.core.queries i)
      (first+i) tiles (retries (first+i)) leader) :
    Wgmma.run ctx oracle code (loopFuel first tiles leader retries n) s = .ok
      ((loopCheckpoint ctx oracle first tiles leader retries s values n).1,
        loopEvents ctx oracle first tiles leader retries s values mapA mapB n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hrun := ih (by omega) (fun i hi => hreplies i (by omega))
    have hready := loopCheckpoint_ready ctx oracle first tiles leader retries s values mapA mapB hr hpc hp hc hregs hacc hfirst n (by omega)
    obtain ⟨hr',hpc',hp',hc',hregs',hacc'⟩ := hready
    have hactive : first+n < tiles := by omega
    simp only [hactive,ite_true] at hpc'
    have hreply := hreplies n (by omega)
    rw [←loopCheckpoint_queries ctx oracle first tiles leader retries s values n] at hreply
    have hstep := iteration_execute ctx oracle (loopCheckpoint ctx oracle first tiles leader retries s values n).1
      (first+n) tiles (retries (first+n)) leader mapA mapB
      (loopCheckpoint ctx oracle first tiles leader retries s values n).2
      hr' hpc' hp' hc' hregs' hacc' hactive hbound hreply.1 hreply.2.1 hreply.2.2
    rw [loopFuel,Wgmma.run_add,hrun]
    simp only [Except.bind,hstep,loopCheckpoint,loopEvents]

theorem full_loop_reaches_output (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (first tiles : Nat)
    (leader : Bool) (retries : Nat → Nat) (s : Wgmma.State) (values : Fin 4 → ℝ) (mapA mapB : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s first tiles leader mapA mapB) (hacc : Accumulators s values)
    (hfirst : first < tiles) :
    (loopCheckpoint ctx oracle first tiles leader retries s values (tiles-first)).1.base.scalar.core.thread.pc = 85 ∧
    Wgmma.pending (loopCheckpoint ctx oracle first tiles leader retries s values (tiles-first)).1.ledger = [] := by
  have h := loopCheckpoint_ready ctx oracle first tiles leader retries s values mapA mapB hr hpc hp hc hregs hacc hfirst
    (tiles-first) (by omega)
  have he : first+(tiles-first) = tiles := by omega
  exact ⟨by simpa [he] using h.2.1,h.2.2.1⟩

theorem iteration_call_count (ctx oracle s tile tiles retries leader values) :
    (iterationState ctx oracle s tile tiles retries leader values).ledger.calls.length = s.ledger.calls.length+1 := by
  have hold : (preparedState s tile tiles retries leader).ledger.calls = s.ledger.calls :=
    congrArg (fun x => x.2.2.1) (preparedState_bookkeeping s tile tiles retries leader)
  change ((preparedState s tile tiles retries leader).ledger.calls++
    [computeCall ctx oracle (preparedState s tile tiles retries leader) (aDescriptor (stage tile)) (bDescriptor (stage tile)) values]).length = _
  simp only [List.length_append,List.length_singleton,hold]

theorem loopCheckpoint_call_count (ctx oracle first tiles leader retries s values n) :
    (loopCheckpoint ctx oracle first tiles leader retries s values n).1.ledger.calls.length = s.ledger.calls.length+n := by
  induction n with
  | zero => simp [loopCheckpoint]
  | succ n ih => simp only [loopCheckpoint,iteration_call_count,ih,Nat.add_succ]

theorem loopCheckpoint_completed (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (first tiles : Nat)
    (leader : Bool) (retries : Nat → Nat) (s : Wgmma.State) (values : Fin 4 → ℝ) (mapA mapB : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s first tiles leader mapA mapB) (hacc : Accumulators s values)
    (hfirst : first < tiles) (n : Nat) (hn : 0 < n) (hcount : first+n ≤ tiles) :
    (loopCheckpoint ctx oracle first tiles leader retries s values n).1.ledger.completed = s.ledger.groups+n := by
  cases n with
  | zero => omega
  | succ n =>
    have hready := loopCheckpoint_ready ctx oracle first tiles leader retries s values mapA mapB
      hr hpc hp hc hregs hacc hfirst n (by omega)
    simp only [loopCheckpoint]
    rw [iterationState_completed _ _ _ _ _ _ _ _ hready.2.2.2.1,loopCheckpoint_groups]
    omega

theorem loopCheckpoint_control_frame (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (first tiles : Nat)
    (leader : Bool) (retries : Nat → Nat) (s : Wgmma.State) (values : Fin 4 → ℝ) (mapA mapB : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s first tiles leader mapA mapB) (hacc : Accumulators s values)
    (hfirst : first < tiles) (n : Nat) (hcount : first+n ≤ tiles) (name : String)
    (hx : name ∉ ["%phase0","%phase1","%even","%waitbar","%ad","%bd","%parity","%ready",
      "%next","%more","%nextbar","%copya","%copyb","%ay","%slot","%tile","%d0","%d1","%d2","%d3"]) :
    lookup name (loopCheckpoint ctx oracle first tiles leader retries s values n).1.base.scalar.core.thread.regs =
      lookup name s.base.scalar.core.thread.regs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hready := loopCheckpoint_ready ctx oracle first tiles leader retries s values mapA mapB
      hr hpc hp hc hregs hacc hfirst n (by omega)
    simp only [loopCheckpoint]
    rw [iterationState_control_frame _ _ _ _ _ _ _ _ hready.2.2.1 hready.2.2.2.1 _ hx,ih (by omega)]

end
end Ptx.Kernels.HopperDoubleBuffer
