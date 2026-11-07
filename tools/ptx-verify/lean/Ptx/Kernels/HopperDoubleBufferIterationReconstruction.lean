import Ptx.Kernels.HopperDoubleBufferLoop
import Ptx.Kernels.HopperDoubleBufferHeaderReconstruction
import Ptx.Kernels.HopperDoubleBufferPreludeReconstruction

/-! Reconstruct one full actual iteration from a completed arbitrary-oracle
source run. Its retries and required TMA lengths are conclusions. Accumulator
availability/loop registers remain explicit; arithmetic and launch admission
are separate, and no whole-loop termination is asserted. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem header_prelude_registers {s tile tiles retries leader mapA mapB}
    (hregs : LoopRegisters s tile tiles leader mapA mapB) :
    PreludeRegisters (headerState s tile retries) tile tiles leader mapA mapB := by
  obtain ⟨hsel,ht,hT,hl,hma,hmb⟩ := hregs
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rwa [headerState_nat_frame _ _ _ "%tile" (by decide)]
  · rwa [headerState_nat_frame _ _ _ "%tiles" (by decide)]
  · rwa [headerState_nat_frame _ _ _ "%leader" (by decide)]
  · rw [headerState_selected_nat _ _ _ "%even" (by decide)]; exact selectionState_even s tile
  · rw [headerState_nat_frame _ _ _ "%bar0" (by decide)]; exact hsel ("%bar0",0) (by simp [selectionBindings])
  · rw [headerState_nat_frame _ _ _ "%bar1" (by decide)]; exact hsel ("%bar1",8) (by simp [selectionBindings])
  · rwa [headerState_nat_frame _ _ _ "%mapa" (by decide)]
  · rwa [headerState_nat_frame _ _ _ "%mapb" (by decide)]

theorem completed_iteration_replies {ctx oracle s count last events tile tiles leader mapA mapB}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hregs : LoopRegisters s tile tiles leader mapA mapB)
    (hlt : tile < tiles) (hbound : tiles ≤ 2^28)
    (hn : Wgmma.run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    ∃ retries, LoopReplies oracle s.base.scalar.core.queries tile tiles retries leader := by
  obtain ⟨retries,hf,ht,_,tail,hsuffix,_⟩ := completed_header_reconstruct hr hpc hp hregs.1 hn hd
  have hshape := completed_prelude_shapes (by simpa using hr) (headerState_pc s tile retries) (by simpa using hp)
    (header_prelude_registers hregs) hlt hbound hsuffix hd
  exact ⟨retries,hf,ht,by simpa only [headerState_queries,Nat.add_assoc] using hshape⟩

theorem completed_iteration_reconstruct {ctx oracle s count last events tile tiles leader mapA mapB values}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 45)
    (hp : Wgmma.pending s.ledger = []) (hc : s.ledger.completed ≤ s.ledger.groups)
    (hregs : LoopRegisters s tile tiles leader mapA mapB) (hacc : Accumulators s values)
    (hlt : tile < tiles) (hbound : tiles ≤ 2^28)
    (hn : Wgmma.run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    ∃ retries, LoopReplies oracle s.base.scalar.core.queries tile tiles retries leader ∧ iterationSteps tile tiles retries leader < count ∧
      ∃ tailEvents, Wgmma.run ctx oracle code (count-iterationSteps tile tiles retries leader)
        (iterationState ctx oracle s tile tiles retries leader values) = .ok (last,tailEvents) ∧
        events = iterationEvents ctx oracle s tile tiles retries leader mapA mapB values++tailEvents := by
  obtain ⟨retries,hreply⟩ := completed_iteration_replies hr hpc hp hregs hlt hbound hn hd
  have hprefix := iteration_execute ctx oracle s tile tiles retries leader mapA mapB values hr hpc hp hc hregs hacc
    hlt hbound hreply.1 hreply.2.1 hreply.2.2
  have hcount := Wgmma.completed_after_running_prefix hn hd hprefix
    ((iterationState_status ctx oracle s tile tiles retries leader values hp hc).trans hr)
  exact ⟨retries,hreply,hcount,Wgmma.run_suffix_of_prefix (Nat.le_of_lt hcount) hn hprefix⟩

end
end Ptx.Kernels.HopperDoubleBuffer
