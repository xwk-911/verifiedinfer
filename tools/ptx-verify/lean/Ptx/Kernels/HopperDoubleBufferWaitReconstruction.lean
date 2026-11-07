import Ptx.Kernels.HopperDoubleBufferWait
import Ptx.Hopper.WgmmaTrace

/-! Invert an actually completed finite execution at the wait loop. A first
successful answer and all preceding failed retries are derived, not assumed.
This is conditional on completion and makes no fairness/termination claim. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem completed_wait_has_success {ctx oracle s count last events bar parity}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 55)
    (hp : Wgmma.pending s.ledger = [])
    (hb : lookup "%waitbar" s.base.scalar.core.thread.regs = some bar)
    (hpar : lookup "%parity" s.base.scalar.core.thread.regs = some parity)
    (hbb : bar < 2^64) (hpb : parity < 2^32)
    (hn : Wgmma.run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    ∃ retries ≤ count, oracle.base.wait (s.base.scalar.core.queries+retries) = true := by
  by_contra hnone
  have hf : ∀ i < count+1, oracle.base.wait (s.base.scalar.core.queries+i) = false := by
    intro i hi
    cases ha : oracle.base.wait (s.base.scalar.core.queries+i) with
    | false => rfl
    | true => exact (hnone ⟨i,by omega,ha⟩).elim
  have hfailed := arbitrary_failed_wait_prefix ctx oracle s bar parity (count+1) hr hpc hp hb hpar hbb hpb hf
  have ht := Wgmma.completed_after_running_prefix hn hd hfailed (by simpa using hr)
  omega

theorem completed_wait_first_success {ctx oracle s count last events bar parity}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 55)
    (hp : Wgmma.pending s.ledger = [])
    (hb : lookup "%waitbar" s.base.scalar.core.thread.regs = some bar)
    (hpar : lookup "%parity" s.base.scalar.core.thread.regs = some parity)
    (hbb : bar < 2^64) (hpb : parity < 2^32)
    (hn : Wgmma.run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    ∃ retries, (∀ i < retries, oracle.base.wait (s.base.scalar.core.queries+i) = false) ∧
      oracle.base.wait (s.base.scalar.core.queries+retries) = true := by
  have hex : ∃ retries, oracle.base.wait (s.base.scalar.core.queries+retries) = true := by
    obtain ⟨r,_,hh⟩ := completed_wait_has_success hr hpc hp hb hpar hbb hpb hn hd
    exact ⟨r,hh⟩
  refine ⟨Nat.find hex,?_,Nat.find_spec hex⟩
  intro i hi
  cases ha : oracle.base.wait (s.base.scalar.core.queries+i) with
  | false => rfl
  | true => exact (Nat.find_min hex hi ha).elim

theorem first_wait_success_unique {oracle : Wgmma.Oracle} {query left right : Nat}
    (hl : ∀ i < left, oracle.base.wait (query+i) = false) (hlt : oracle.base.wait (query+left) = true)
    (hr : ∀ i < right, oracle.base.wait (query+i) = false) (hrt : oracle.base.wait (query+right) = true) : left = right := by
  rcases lt_trichotomy left right with h | h | h
  · have hh := hr left h; rw [hlt] at hh; cases hh
  · exact h
  · have hh := hl right h; rw [hrt] at hh; cases hh

theorem wait_success_prefix (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State) (bar parity retries : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 55)
    (hp : Wgmma.pending s.ledger = [])
    (hb : lookup "%waitbar" s.base.scalar.core.thread.regs = some bar)
    (hpar : lookup "%parity" s.base.scalar.core.thread.regs = some parity)
    (hbb : bar < 2^64) (hpb : parity < 2^32)
    (hf : ∀ i < retries, oracle.base.wait (s.base.scalar.core.queries+i) = false)
    (ht : oracle.base.wait (s.base.scalar.core.queries+retries) = true) :
    Wgmma.run ctx oracle code (2*retries+2) s = .ok
      (testedState (retryState retries s) true,List.replicate retries (waitEvent ctx bar parity false)++[waitEvent ctx bar parity true]) := by
  have hfailed := arbitrary_failed_wait_prefix ctx oracle s bar parity retries hr hpc hp hb hpar hbb hpb hf
  have htest := wait_test_execute ctx oracle (retryState retries s) bar parity
    (by simpa using hr) (retryState_pc retries s hpc) (by simpa using hp)
    (by simpa only [retryState_nat retries s "%waitbar" (by decide)] using hb)
    (by simpa only [retryState_nat retries s "%parity" (by decide)] using hpar) hbb hpb
  rw [retryState_queries,ht] at htest
  rw [Wgmma.run_add,hfailed]
  simp only [Except.bind,htest]

theorem completed_wait_reconstruct {ctx oracle s count last events bar parity}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 55)
    (hp : Wgmma.pending s.ledger = [])
    (hb : lookup "%waitbar" s.base.scalar.core.thread.regs = some bar)
    (hpar : lookup "%parity" s.base.scalar.core.thread.regs = some parity)
    (hbb : bar < 2^64) (hpb : parity < 2^32)
    (hn : Wgmma.run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    ∃ retries, (∀ i < retries, oracle.base.wait (s.base.scalar.core.queries+i) = false) ∧
      oracle.base.wait (s.base.scalar.core.queries+retries) = true ∧ 2*retries+2 < count ∧
      ∃ tailEvents, Wgmma.run ctx oracle code (count-(2*retries+2)) (testedState (retryState retries s) true) = .ok (last,tailEvents) ∧
        events = (List.replicate retries (waitEvent ctx bar parity false)++[waitEvent ctx bar parity true])++tailEvents := by
  obtain ⟨retries,hf,ht⟩ := completed_wait_first_success hr hpc hp hb hpar hbb hpb hn hd
  have hprefix := wait_success_prefix ctx oracle s bar parity retries hr hpc hp hb hpar hbb hpb hf ht
  have hcount := Wgmma.completed_after_running_prefix hn hd hprefix (by simpa using hr)
  exact ⟨retries,hf,ht,hcount,Wgmma.run_suffix_of_prefix (Nat.le_of_lt hcount) hn hprefix⟩

theorem never_ready_cannot_complete {ctx oracle s bar parity}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 55)
    (hp : Wgmma.pending s.ledger = [])
    (hb : lookup "%waitbar" s.base.scalar.core.thread.regs = some bar)
    (hpar : lookup "%parity" s.base.scalar.core.thread.regs = some parity)
    (hbb : bar < 2^64) (hpb : parity < 2^32)
    (hnever : ∀ i, oracle.base.wait (s.base.scalar.core.queries+i) = false) :
    ¬∃ count last events, Wgmma.run ctx oracle code count s = .ok (last,events) ∧ last.base.scalar.core.thread.status = .done := by
  rintro ⟨count,last,events,hn,hd⟩
  obtain ⟨r,_,hs⟩ := completed_wait_has_success hr hpc hp hb hpar hbb hpb hn hd
  rw [hnever] at hs
  cases hs

end
end Ptx.Kernels.HopperDoubleBuffer
