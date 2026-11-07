import Ptx.Kernels.HopperDoubleBufferPrefetchTransfer
import Ptx.Hopper.WgmmaTmaInversion

/-! Reconstruct required TMA lengths from an actually completed producer run
at PC 73. Values/descriptors remain arbitrary. These are source facts only;
issuing the copies does not admit completed/published bytes or resource reuse.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem prefetch_arrival_prefix (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State) (slot : Stage)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 73)
    (hp : Wgmma.pending s.ledger = [])
    (hbar : lookup "%nextbar" s.base.scalar.core.thread.regs = some (barrierAddress slot)) :
    Wgmma.run ctx oracle code 1 s = .ok
      (prefetchArrived s,[.base (.barrier ⟨⟨.shared ctx.id.cta,barrierAddress slot⟩,.arriveExpectTx 2304⟩)]) := by
  have hbound : barrierAddress slot < 2^64 := by have := slot.isLt; dsimp [barrierAddress]; omega
  have hs := Wgmma.arrive_expect_step (ctx := ctx) (oracle := oracle) (code := code) (count := .imm 2304) hr
    (by simp [hpc,code,Generated.hopper_double_buffer_gemm.program]) hp
    (eval_register_address ctx s "%nextbar" _ hbar hbound) rfl
  have hs' : Wgmma.step ctx oracle code s = .ok
      (prefetchArrived s,[.base (.barrier ⟨⟨.shared ctx.id.cta,barrierAddress slot⟩,.arriveExpectTx 2304⟩)]) := by
    simpa only [prefetchArrived,prefetchArrive,show wrap 32 2304 = 2304 from by decide] using hs
  simp only [Wgmma.run,hs',Except.bind,List.append_nil]

theorem prefetch_a_prefix (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (slot : Stage) (next mapA : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 73)
    (hp : Wgmma.pending s.ledger = [])
    (hbar : lookup "%nextbar" s.base.scalar.core.thread.regs = some (barrierAddress slot))
    (ha : lookup "%copya" s.base.scalar.core.thread.regs = some (aBase slot))
    (hma : lookup "%mapa" s.base.scalar.core.thread.regs = some mapA)
    (hay : lookup "%ay" s.base.scalar.core.thread.regs = some (8*next))
    (hshape : (oracle.base.tmaBytes (s.base.scalar.core.queries+1)).length = (oracle.base.descriptor s.base.scalar.core.queries).bytes) :
    Wgmma.run ctx oracle code 2 s = .ok
      (prefetchAIssued s,[.base (.barrier ⟨⟨.shared ctx.id.cta,barrierAddress slot⟩,.arriveExpectTx 2304⟩),
        .base (.tmaIssue (prefetchACopy oracle s slot next mapA))]) := by
  have h0 := prefetch_arrival_prefix ctx oracle s slot hr hpc hp hbar
  have hbound : barrierAddress slot < 2^64 := by have := slot.isLt; dsimp [barrierAddress]; omega
  have habound : aBase slot < 2^64 := by have := slot.isLt; dsimp [aBase]; omega
  have h1 := Wgmma.tma_issue_step (ctx := ctx) (oracle := oracle) (s := prefetchArrived s)
    (dstAddr := aBase slot) (descriptorAddr := mapA) (px := 0) (py := 8*next) (barrierAddr := barrierAddress slot)
    (by simpa [prefetchArrived] using hr)
    (show code[(prefetchArrived s).base.scalar.core.thread.pc]? = some prefetchAInstruction by simp [prefetchArrived,hpc,prefetchAInstruction,code,Generated.hopper_double_buffer_gemm.program])
    (by simpa [prefetchArrived] using hp)
    (eval_register_address ctx (prefetchArrived s) "%copya" _ (by simpa [prefetchArrived] using ha) habound)
    (by simp [Ptx.eval,prefetchArrived,hma]) rfl (by simp [Ptx.eval,prefetchArrived,hay])
    (eval_register_address ctx (prefetchArrived s) "%nextbar" _ (by simpa [prefetchArrived] using hbar) hbound)
    (by simpa [prefetchArrived] using hshape)
  have h1' : Wgmma.step ctx oracle code (prefetchArrived s) = .ok
      (prefetchAIssued s,[.base (.tmaIssue (prefetchACopy oracle s slot next mapA))]) := by
    simpa [prefetchAIssued,prefetchACopy,prefetchArrived,prefetchAInstruction,show Tma.signed32 0 = 0 from by decide] using h1
  rw [show 2 = 1+1 from rfl,Wgmma.run_add,h0]
  simp only [Except.bind,Wgmma.run,h1',List.nil_append,List.cons_append,List.append_nil]

theorem completed_transfer_shapes {ctx oracle s count last events slot next mapA}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 73)
    (hp : Wgmma.pending s.ledger = [])
    (hbar : lookup "%nextbar" s.base.scalar.core.thread.regs = some (barrierAddress slot))
    (ha : lookup "%copya" s.base.scalar.core.thread.regs = some (aBase slot))
    (hma : lookup "%mapa" s.base.scalar.core.thread.regs = some mapA)
    (hay : lookup "%ay" s.base.scalar.core.thread.regs = some (8*next))
    (hn : Wgmma.run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    (oracle.base.tmaBytes (s.base.scalar.core.queries+1)).length = (oracle.base.descriptor s.base.scalar.core.queries).bytes ∧
    (oracle.base.tmaBytes (s.base.scalar.core.queries+3)).length = (oracle.base.descriptor (s.base.scalar.core.queries+2)).bytes := by
  have h0 := prefetch_arrival_prefix ctx oracle s slot hr hpc hp hbar
  have hA := Wgmma.completed_tma_shape_after_prefix hn hd h0 (by simpa [prefetchArrived] using hr)
    (show code[(prefetchArrived s).base.scalar.core.thread.pc]? = some prefetchAInstruction by simp [prefetchArrived,hpc,prefetchAInstruction,code,Generated.hopper_double_buffer_gemm.program])
  simp only [prefetchArrived,Wgmma.advanceOrdinary_queries] at hA
  have h1 := prefetch_a_prefix ctx oracle s slot next mapA hr hpc hp hbar ha hma hay hA
  have hB := Wgmma.completed_tma_shape_after_prefix hn hd h1 (by simpa [prefetchAIssued,prefetchArrived] using hr)
    (show code[(prefetchAIssued s).base.scalar.core.thread.pc]? = some prefetchBInstruction by simp [prefetchAIssued,prefetchArrived,hpc,prefetchBInstruction,code,Generated.hopper_double_buffer_gemm.program])
  exact ⟨hA,by simpa only [prefetchAIssued,prefetchArrived,Wgmma.tmaState_queries,Wgmma.advanceOrdinary_queries,Nat.add_assoc] using hB⟩

end
end Ptx.Kernels.HopperDoubleBuffer
