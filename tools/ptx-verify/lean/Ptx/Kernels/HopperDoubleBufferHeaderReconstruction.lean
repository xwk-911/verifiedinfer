import Ptx.Kernels.HopperDoubleBufferHeader
import Ptx.Kernels.HopperDoubleBufferWaitReconstruction

/-! A completed arbitrary-oracle run from the loop head determines its own
retry count. Exact state/events after selection, waits and phase update are
reconstructed; no chosen retry schedule, fairness or eventual completion is
assumed. The remainder of the iteration/kernel still needs reconstruction. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem completed_header_reconstruct {ctx oracle s count last events tile}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hregs : SelectionReady s tile)
    (hn : Wgmma.run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    ∃ retries, (∀ i < retries, oracle.base.wait (s.base.scalar.core.queries+i) = false) ∧
      oracle.base.wait (s.base.scalar.core.queries+retries) = true ∧ headerSteps tile retries < count ∧
      ∃ tailEvents, Wgmma.run ctx oracle code (count-headerSteps tile retries) (headerState s tile retries) = .ok (last,tailEvents) ∧
        events = (List.replicate retries (waitEvent ctx (barrierAddress (stage tile)) (expectedParity tile) false)++
          [waitEvent ctx (barrierAddress (stage tile)) (expectedParity tile) true])++tailEvents := by
  have hselection := selection_execute ctx oracle s tile hr hpc hp hregs
  have hc := Wgmma.completed_after_running_prefix hn hd hselection (by simpa using hr)
  obtain ⟨remaining,hsuffix,_⟩ := Wgmma.run_suffix_of_prefix (Nat.le_of_lt hc) hn hselection
  obtain ⟨hbar,_,_,hpar⟩ := selectionState_operands s tile
  have hbb : barrierAddress (stage tile) < 2^64 := by
    have hs := (stage tile).isLt
    dsimp [barrierAddress]; omega
  have hpb : expectedParity tile < 2^32 := by have := expected_parity_bounded tile; omega
  obtain ⟨retries,hf,ht⟩ := completed_wait_first_success (by simpa using hr) (by simp) (by simpa using hp)
    hbar hpar hbb hpb hsuffix hd
  simp only [selectionState_queries] at hf ht
  have hheader := header_execute ctx oracle s tile retries hr hpc hp hregs hf ht
  have hcount := Wgmma.completed_after_running_prefix hn hd hheader (by simpa using hr)
  exact ⟨retries,hf,ht,hcount,Wgmma.run_suffix_of_prefix (Nat.le_of_lt hcount) hn hheader⟩

theorem header_never_ready_cannot_complete {ctx oracle s tile}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hregs : SelectionReady s tile)
    (hnever : ∀ i, oracle.base.wait (s.base.scalar.core.queries+i) = false) :
    ¬∃ count last events, Wgmma.run ctx oracle code count s = .ok (last,events) ∧ last.base.scalar.core.thread.status = .done := by
  rintro ⟨count,last,events,hn,hd⟩
  obtain ⟨r,_,hs,_⟩ := completed_header_reconstruct hr hpc hp hregs hn hd
  rw [hnever] at hs
  cases hs

end
end Ptx.Kernels.HopperDoubleBuffer
