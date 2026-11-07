import Ptx.Kernels.HopperDoubleBufferHeaderReconstruction
import Ptx.Kernels.HopperDoubleBufferDataSource
import Ptx.Kernels.HopperDoubleBufferProbeMetadata

/-! A real completed generated-source suffix with three failed waits exercises
inverse reconstruction, and count padding/truncation is rejected. Metadata
checks never decide equality of full real-valued states or event payloads. -/
namespace Ptx.HopperSourceReconstructionTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryOracle : Wgmma.Oracle := {oracle 1 with base := {(oracle 1).base with wait := fun q => decide (3 ≤ q)}}
def headerStart : Wgmma.State := initialLoopState 1 127 false
def waitStart : Wgmma.State := selectionState headerStart 0
def headerCount : Nat := completeSteps 1 127-initialSteps false+6
def waitCount : Nat := headerCount-selectionSteps 0
def waitRun := Wgmma.run (ctx 1 127) retryOracle code waitCount waitStart
def waitResult : Wgmma.State × List Wgmma.Event := waitRun.toOption.getD ({},[])

theorem wait_source_succeeds : waitRun.toOption.isSome = true := by decide
theorem wait_source_done_metadata : (waitResult.1.base.scalar.core.thread.status == .done) = true := by decide
theorem wait_source_produced : waitRun = .ok waitResult := by
  cases hs : waitRun with
  | error fault => have hh := wait_source_succeeds; rw [hs] at hh; cases hh
  | ok value => simp only [waitResult,hs,Except.toOption,Option.getD_some]
theorem wait_source_done : waitResult.1.base.scalar.core.thread.status = .done := by
  simpa only [beq_iff_eq] using wait_source_done_metadata
theorem failed_wait_events_retained : (waitResult.2.filterMap waitMetadata).take 4 =
    [(0,0,false),(0,0,false),(0,0,false),(0,0,true)] := by decide

theorem actual_first_success_conditions :
    (∀ i < 3, retryOracle.base.wait (waitStart.base.scalar.core.queries+i) = false) ∧
      retryOracle.base.wait (waitStart.base.scalar.core.queries+3) = true := by
  refine ⟨?_,by decide⟩
  intro i hi
  change decide (3 ≤ 0+i) = false
  simp only [decide_eq_false_iff_not]
  omega

theorem actual_wait_retry_count_reconstructed :
    ∃ tailEvents, Wgmma.run (ctx 1 127) retryOracle code (waitCount-8) (testedState (retryState 3 waitStart) true) =
      .ok (waitResult.1,tailEvents) ∧
      waitResult.2 = (List.replicate 3 (waitEvent (ctx 1 127) 0 0 false)++[waitEvent (ctx 1 127) 0 0 true])++tailEvents := by
  obtain ⟨r,hf,ht,_,hs⟩ := completed_wait_reconstruct (ctx := ctx 1 127) (oracle := retryOracle)
    (s := waitStart) (by rfl) (by rfl) (by rfl) (bar := 0) (parity := 0) (by rfl) (by rfl)
    (by decide) (by decide) wait_source_produced wait_source_done
  have he := first_wait_success_unique hf ht actual_first_success_conditions.1 actual_first_success_conditions.2
  subst r
  exact hs

theorem cannot_complete_before_successful_wait {count last events} (hb : count ≤ 8) :
    ¬(Wgmma.run (ctx 1 127) retryOracle code count waitStart = .ok (last,events) ∧ last.base.scalar.core.thread.status = .done) := by
  rintro ⟨hn,hd⟩
  obtain ⟨r,hf,ht,hcount,_⟩ := completed_wait_reconstruct (ctx := ctx 1 127) (oracle := retryOracle)
    (s := waitStart) (by rfl) (by rfl) (by rfl) (bar := 0) (parity := 0) (by rfl) (by rfl)
    (by decide) (by decide) hn hd
  have he := first_wait_success_unique hf ht actual_first_success_conditions.1 actual_first_success_conditions.2
  omega

theorem actual_header_produced :
    Wgmma.run (ctx 1 127) retryOracle code headerCount headerStart = .ok waitResult := by
  have hregs : SelectionReady headerStart 0 := (initial_loop_registers 1 127 false (by decide)).1
  have hsel := selection_execute (ctx 1 127) retryOracle headerStart 0 (by rfl) (by rfl) (by rfl) hregs
  rw [show headerCount = selectionSteps 0+waitCount by decide,Wgmma.run_add,hsel]
  simp only [Except.bind]
  have hwait : Wgmma.run (ctx 1 127) retryOracle code waitCount (selectionState headerStart 0) = .ok waitResult := wait_source_produced
  rw [hwait]
  simp only [List.nil_append,Prod.eta]

theorem actual_header_retry_count_reconstructed {count last events}
    (hn : Wgmma.run (ctx 1 127) retryOracle code count headerStart = .ok (last,events))
    (hd : last.base.scalar.core.thread.status = .done) :
    ∃ tailEvents, Wgmma.run (ctx 1 127) retryOracle code (count-headerSteps 0 3) (headerState headerStart 0 3) = .ok (last,tailEvents) ∧
      events = (List.replicate 3 (waitEvent (ctx 1 127) 0 0 false)++[waitEvent (ctx 1 127) 0 0 true])++tailEvents := by
  have hregs : SelectionReady headerStart 0 := (initial_loop_registers 1 127 false (by decide)).1
  obtain ⟨r,hf,ht,_,hs⟩ := completed_header_reconstruct (by rfl) (by rfl) (by rfl) hregs hn hd
  have he := first_wait_success_unique hf ht actual_first_success_conditions.1 actual_first_success_conditions.2
  subst r
  exact hs

theorem never_ready_header_rejected :
    ¬∃ count last events, Wgmma.run (ctx 1 127)
      ({retryOracle with base := {retryOracle.base with wait := fun _ => false}} : Wgmma.Oracle) code count headerStart = .ok (last,events) ∧
      last.base.scalar.core.thread.status = .done := by
  exact header_never_ready_cannot_complete (by rfl) (by rfl) (by rfl)
    (initial_loop_registers 1 127 false (by decide)).1 (fun _ => rfl)

theorem canonical_complete_run_count_unique (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) (hb : tiles ≤ 2^28)
    {count last events} (hn : Wgmma.run (ctx tiles lane) (dataOracle a b tiles lane) code count {} = .ok (last,events))
    (hd : last.base.scalar.core.thread.status = .done) :
    count = completeSteps tiles lane ∧ last = dataCompleteState a b tiles lane ∧ events = dataCompleteEvents a b tiles lane :=
  Wgmma.complete_run_unique hn hd (data_complete_run a b tiles lane hb) (data_complete_local a b tiles lane hb).1

theorem padded_complete_run_rejected (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) (hb : tiles ≤ 2^28) :
    Wgmma.run (ctx tiles lane) (dataOracle a b tiles lane) code (completeSteps tiles lane+1) {} = .error .blocked := by
  rw [Wgmma.run_add,data_complete_run a b tiles lane hb]
  simp only [Except.bind,Wgmma.run_done_suffix (data_complete_local a b tiles lane hb).1 0]

end
end Ptx.HopperSourceReconstructionTests
