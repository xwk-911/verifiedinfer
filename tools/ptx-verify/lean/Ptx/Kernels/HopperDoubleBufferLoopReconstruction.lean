import Ptx.Kernels.HopperDoubleBufferLoopLocality
import Ptx.Kernels.HopperDoubleBufferIterationReconstruction

/-! Reconstruct every iteration of an actually completed arbitrary-oracle
loop run. The retry schedule is extracted, not prescribed. This is conditional
source reconstruction from the loop invariant, not termination, initial/output
reconstruction, tensor correctness or full memory/resource admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem completed_loop_reply_prefix {ctx oracle s count last events first tiles leader mapA mapB values}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s first tiles leader mapA mapB) (hacc : Accumulators s values)
    (hfirst : first < tiles) (hbound : tiles ≤ 2^28)
    (hn : Wgmma.run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done)
    (n : Nat) (hcount : first+n ≤ tiles) :
    ∃ retries, ∀ i < n, LoopReplies oracle (loopQuery first tiles leader retries s.base.scalar.core.queries i)
      (first+i) tiles (retries (first+i)) leader := by
  induction n with
  | zero => exact ⟨fun _ => 0,by intro i hi; omega⟩
  | succ n ih =>
    obtain ⟨retries,hreplies⟩ := ih (by omega)
    have hprefix := loop_execute ctx oracle first tiles leader retries s values mapA mapB hr hpc hp hc hregs hacc
      hfirst hbound n (by omega) hreplies
    have hready := loopCheckpoint_ready ctx oracle first tiles leader retries s values mapA mapB hr hpc hp hc hregs hacc hfirst n (by omega)
    have hfuel := Wgmma.completed_after_running_prefix hn hd hprefix hready.1
    obtain ⟨tail,hsuffix,_⟩ := Wgmma.run_suffix_of_prefix (Nat.le_of_lt hfuel) hn hprefix
    have hactive : first+n < tiles := by omega
    obtain ⟨retry,hreply⟩ := completed_iteration_replies hready.1 (by simpa only [hactive,ite_true] using hready.2.1)
      hready.2.2.1 hready.2.2.2.2.1 hactive hbound hsuffix hd
    let updated := Function.update retries (first+n) retry
    have hagree : ∀ i < n, updated (first+i) = retries (first+i) := by
      intro i hi
      exact Function.update_of_ne (by omega) _ _
    refine ⟨updated,?_⟩
    intro i hi
    by_cases hold : i < n
    · have hquery := loop_query_retry_congr (tiles := tiles) (leader := leader) (n := i)
        (query := s.base.scalar.core.queries) (fun j hj => hagree j (by omega : j < n))
      rw [hquery,hagree i hold]
      exact hreplies i hold
    · have heq : i = n := by omega
      subst i
      have hquery := loop_query_retry_congr (tiles := tiles) (leader := leader) (query := s.base.scalar.core.queries) hagree
      rw [hquery]
      have hvalue : updated (first+n) = retry := Function.update_self _ _ _
      rw [hvalue]
      simpa only [loopCheckpoint_queries] using hreply

theorem completed_loop_reconstruct {ctx oracle s count last events first tiles leader mapA mapB values}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s first tiles leader mapA mapB) (hacc : Accumulators s values)
    (hfirst : first < tiles) (hbound : tiles ≤ 2^28)
    (hn : Wgmma.run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    ∃ retries, (∀ i < tiles-first, LoopReplies oracle (loopQuery first tiles leader retries s.base.scalar.core.queries i)
      (first+i) tiles (retries (first+i)) leader) ∧
      loopFuel first tiles leader retries (tiles-first) < count ∧
      (loopCheckpoint ctx oracle first tiles leader retries s values (tiles-first)).1.base.scalar.core.thread.pc = 85 ∧
      Wgmma.pending (loopCheckpoint ctx oracle first tiles leader retries s values (tiles-first)).1.ledger = [] ∧
      ∃ tailEvents, Wgmma.run ctx oracle code (count-loopFuel first tiles leader retries (tiles-first))
        (loopCheckpoint ctx oracle first tiles leader retries s values (tiles-first)).1 = .ok (last,tailEvents) ∧
        events = loopEvents ctx oracle first tiles leader retries s values mapA mapB (tiles-first)++tailEvents := by
  obtain ⟨retries,hreplies⟩ := completed_loop_reply_prefix hr hpc hp hc hregs hacc hfirst hbound hn hd (tiles-first) (by omega)
  have hprefix := loop_execute ctx oracle first tiles leader retries s values mapA mapB hr hpc hp hc hregs hacc
    hfirst hbound (tiles-first) (by omega) hreplies
  have hready := loopCheckpoint_ready ctx oracle first tiles leader retries s values mapA mapB hr hpc hp hc hregs hacc
    hfirst (tiles-first) (by omega)
  have hfuel := Wgmma.completed_after_running_prefix hn hd hprefix hready.1
  have houtput : (loopCheckpoint ctx oracle first tiles leader retries s values (tiles-first)).1.base.scalar.core.thread.pc = 85 := by
    simpa only [show first+(tiles-first) = tiles by omega,lt_self_iff_false,ite_false] using hready.2.1
  exact ⟨retries,hreplies,hfuel,houtput,hready.2.2.1,Wgmma.run_suffix_of_prefix (Nat.le_of_lt hfuel) hn hprefix⟩

theorem loop_reply_schedules_unique {oracle first tiles leader left right query n}
    (hl : ∀ i < n, LoopReplies oracle (loopQuery first tiles leader left query i) (first+i) tiles (left (first+i)) leader)
    (hr : ∀ i < n, LoopReplies oracle (loopQuery first tiles leader right query i) (first+i) tiles (right (first+i)) leader) :
    ∀ i < n, left (first+i) = right (first+i) := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have hprefix := ih (fun i hi => hl i (by omega)) (fun i hi => hr i (by omega))
    intro i hi
    by_cases hold : i < n
    · exact hprefix i hold
    · have heq : i = n := by omega
      subst i
      have hquery := loop_query_retry_congr (tiles := tiles) (leader := leader) (query := query) hprefix
      have hleft := hl n (by omega)
      have hright := hr n (by omega)
      rw [← hquery] at hright
      exact first_wait_success_unique hleft.1 hleft.2.1 hright.1 hright.2.1

theorem completed_loop_reconstruct_at_schedule {ctx oracle s count last events first tiles leader mapA mapB values retries}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s first tiles leader mapA mapB) (hacc : Accumulators s values)
    (hfirst : first < tiles) (hbound : tiles ≤ 2^28)
    (hn : Wgmma.run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done)
    (hreplies : ∀ i < tiles-first, LoopReplies oracle (loopQuery first tiles leader retries s.base.scalar.core.queries i)
      (first+i) tiles (retries (first+i)) leader) :
    loopFuel first tiles leader retries (tiles-first) < count ∧
      (loopCheckpoint ctx oracle first tiles leader retries s values (tiles-first)).1.base.scalar.core.thread.pc = 85 ∧
      Wgmma.pending (loopCheckpoint ctx oracle first tiles leader retries s values (tiles-first)).1.ledger = [] ∧
      ∃ tailEvents, Wgmma.run ctx oracle code (count-loopFuel first tiles leader retries (tiles-first))
        (loopCheckpoint ctx oracle first tiles leader retries s values (tiles-first)).1 = .ok (last,tailEvents) ∧
        events = loopEvents ctx oracle first tiles leader retries s values mapA mapB (tiles-first)++tailEvents := by
  obtain ⟨extracted,hex,hfuel,houtput,hpending,htail⟩ := completed_loop_reconstruct hr hpc hp hc hregs hacc hfirst hbound hn hd
  have he := loop_reply_schedules_unique hex hreplies
  have hf := loop_fuel_retry_congr (tiles := tiles) (leader := leader) he
  have hs := loop_checkpoint_retry_congr (ctx := ctx) (oracle := oracle) (tiles := tiles) (leader := leader) (s := s) (values := values) he
  have hev := loop_events_retry_congr (ctx := ctx) (oracle := oracle) (tiles := tiles) (leader := leader)
    (s := s) (values := values) (mapA := mapA) (mapB := mapB) he
  rw [hf] at hfuel htail
  rw [hs] at houtput hpending htail
  rw [hev] at htail
  exact ⟨hfuel,houtput,hpending,htail⟩

end
end Ptx.Kernels.HopperDoubleBuffer
