import Ptx.ISA.BarrierSites
import Ptx.Kernels.BarrierPublish
import Ptx.Generated.SharedSwap
import Ptx.Generated.DivergentBarrier

/-! Publication now uses a common aligned barrier site. The archived divergent
fixture remains a negative convergence example, not a GPU-positive case. These
source facts do not close the generic model's full PTX legality boundary. -/
namespace Ptx.BarrierSitesTests
open Ptx.ISA Ptx.Event

theorem publication_common_site : barrierSites Generated.barrier_publish.program 0 = [7] := by decide
theorem shared_swap_common_site : barrierSites Generated.shared_swap.program 0 = [10] := by decide
theorem divergent_sites : barrierSites Generated.divergent_barrier.program 0 = [5,9] := by decide

theorem divergent_not_single_site : ¬ ∃ pc, barrierSites Generated.divergent_barrier.program 0 = [pc] := by
  rintro ⟨pc,h⟩
  rw [divergent_sites] at h
  have hl := congrArg List.length h
  simp at hl

def writerBefore (base value : Nat) : Event.State := {
  thread := {pc := 9,regs := [("%p",1),("%i",0),("%v",wrap 32 value),("%d",wrap 64 base)]}
}
def readerBefore (base value : Nat) : Event.State := {
  thread := {pc := 5,regs := [("%p",0),("%i",1),("%v",wrap 32 value),("%d",wrap 64 base)]}
}

theorem divergent_writer_reaches_site (base value : Nat) (oracle : Event.Oracle) :
    Event.run ⟨BarrierPublish.writer,BarrierPublish.params base value⟩ oracle Generated.divergent_barrier.program 6 {} =
      .ok (writerBefore base value,[.write (BarrierPublish.loc base) (BarrierPublish.bytes value)]) := by
  simp [Generated.divergent_barrier.program,BarrierPublish.params,writerBefore,Event.run,Event.step,
    localStep,eval,evalAddr,assign,advance,put,lookup,wrap,BarrierPublish.writer,Dim3.zero,
    BarrierPublish.loc,BarrierPublish.bytes,Location.resolve,bind,Except.bind,pure,Except.pure]

theorem divergent_reader_reaches_site (base value : Nat) (oracle : Event.Oracle) :
    Event.run ⟨BarrierPublish.reader,BarrierPublish.params base value⟩ oracle Generated.divergent_barrier.program 5 {} =
      .ok (readerBefore base value,[]) := by
  simp [Generated.divergent_barrier.program,BarrierPublish.params,readerBefore,Event.run,Event.step,
    localStep,eval,evalAddr,assign,advance,put,lookup,wrap,BarrierPublish.reader,Dim3.zero,
    bind,Except.bind,pure,Except.pure]

theorem same_id_different_instructions (base value : Nat) :
    Generated.divergent_barrier.program[(writerBefore base value).thread.pc]? = some (.barrier 0) ∧
    Generated.divergent_barrier.program[(readerBefore base value).thread.pc]? = some (.barrier 0) ∧
    (writerBefore base value).thread.pc ≠ (readerBefore base value).thread.pc :=
  ⟨rfl,rfl,by change (9 : Nat) ≠ 5; decide⟩

end Ptx.BarrierSitesTests
