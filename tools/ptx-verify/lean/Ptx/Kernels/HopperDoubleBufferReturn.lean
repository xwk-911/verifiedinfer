import Ptx.Kernels.HopperDoubleBufferOutputStores

/-! Actual PCs 96..100: final CTA barrier, producer-only invalidation and ret.
Source completion does not establish legal resource invalidation, memory
visibility or observable kernel results without the separate graph conditions.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def returnedState (s : Wgmma.State) (leader : Bool) : Wgmma.State :=
  let synced := Wgmma.barrierState s 1
  let branched := Wgmma.integerPC synced (.branch "%leader" false 100) (if leader then 98 else 100)
  let invalidated := if leader then
    Wgmma.advanceOrdinary (Wgmma.advanceOrdinary branched (.mbarrierInval ⟨.reg "%bar0",0⟩)) (.mbarrierInval ⟨.reg "%bar1",0⟩)
    else branched
  Wgmma.returnState invalidated

def returnEvents (context : Scalar.Context) (s : Wgmma.State) (leader : Bool) : List Wgmma.Event :=
  [.base (.ampere (.ordinary (.barrierArrival 1 (Ptx.Event.generation s.base.scalar.core 1)))),
   .base (.ampere (.ordinary (.barrierReturn 1 (Ptx.Event.generation s.base.scalar.core 1))))]++
  (if leader then [.base (.barrier ⟨⟨.shared context.id.cta,0⟩,.inval⟩),.base (.barrier ⟨⟨.shared context.id.cta,8⟩,.inval⟩)] else [])
def returnSteps (leader : Bool) : Nat := if leader then 5 else 3

theorem output_return_execute (context : Scalar.Context) (reply : Wgmma.Oracle) (s : Wgmma.State) (leader : Bool)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 96)
    (hp : Wgmma.pending s.ledger = [])
    (hl : lookup "%leader" s.base.scalar.core.thread.regs = some (if leader then 1 else 0))
    (hb0 : lookup "%bar0" s.base.scalar.core.thread.regs = some 0)
    (hb1 : lookup "%bar1" s.base.scalar.core.thread.regs = some 8) :
    Wgmma.run context reply code (returnSteps leader) s = .ok (returnedState s leader,returnEvents context s leader) := by
  let s1 := Wgmma.barrierState s 1
  let s2 := Wgmma.integerPC s1 (.branch "%leader" false 100) (if leader then 98 else 100)
  have h0 : Wgmma.step context reply code s = .ok
      (s1,[.base (.ampere (.ordinary (.barrierArrival 1 (Ptx.Event.generation s.base.scalar.core 1)))),
       .base (.ampere (.ordinary (.barrierReturn 1 (Ptx.Event.generation s.base.scalar.core 1))))]) :=
    Wgmma.barrier_step hr (by simp [hpc,code,Generated.hopper_double_buffer_gemm.program])
  have h1 : Wgmma.step context reply code s1 = .ok (s2,[]) := by
    have hs := Wgmma.branch_step (ctx := context) (oracle := reply) (code := code)
      (by simp [s1,hr])
      (show code[s1.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.branch "%leader" false 100)))) by simp [s1,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1] using hp) (show lookup "%leader" s1.base.scalar.core.thread.regs = some (if leader then 1 else 0) by simpa [s1] using hl)
    cases leader <;> simpa [s2,s1,hpc] using hs
  cases leader with
  | false =>
    have h2 : Wgmma.step context reply code s2 = .ok (returnedState s false,[]) := by
      exact Wgmma.return_step (by simp [s2,s1,hr]) (by simp [s2,code,Generated.hopper_double_buffer_gemm.program]) (by simpa [s2,s1] using hp)
    dsimp only [s2,s1] at h0 h1 h2
    simp only [Bool.false_eq_true,ite_true,ite_false] at h0 h1 h2
    simp only [returnSteps,returnedState,returnEvents,Bool.false_eq_true,Wgmma.run,h0,h1,h2,Except.bind,ite_false,List.nil_append,List.cons_append,List.append_nil]
  | true =>
    let s3 := Wgmma.advanceOrdinary s2 (.mbarrierInval ⟨.reg "%bar0",0⟩)
    let s4 := Wgmma.advanceOrdinary s3 (.mbarrierInval ⟨.reg "%bar1",0⟩)
    have h2 : Wgmma.step context reply code s2 = .ok (s3,[.base (.barrier ⟨⟨.shared context.id.cta,0⟩,.inval⟩)]) := by
      apply Wgmma.invalidate_step (by simp [s2,s1,hr])
        (by simp [s2,code,Generated.hopper_double_buffer_gemm.program]) (by simpa [s2,s1] using hp)
      exact eval_register_address context s2 "%bar0" 0 (by simpa [s2,s1] using hb0) (by decide)
    have h3 : Wgmma.step context reply code s3 = .ok (s4,[.base (.barrier ⟨⟨.shared context.id.cta,8⟩,.inval⟩)]) := by
      apply Wgmma.invalidate_step (by simp [s3,s2,s1,hr])
        (by simp [s3,s2,code,Generated.hopper_double_buffer_gemm.program]) (by simpa [s3,s2,s1] using hp)
      exact eval_register_address context s3 "%bar1" 8 (by simpa [s3,s2,s1] using hb1) (by decide)
    have h4 : Wgmma.step context reply code s4 = .ok (returnedState s true,[]) := by
      exact Wgmma.return_step (by simp [s4,s3,s2,s1,hr]) (by simp [s4,s3,s2,code,Generated.hopper_double_buffer_gemm.program]) (by simpa [s4,s3,s2,s1] using hp)
    dsimp only [s4,s3,s2,s1] at h0 h1 h2 h3 h4
    simp only [Bool.false_eq_true,ite_true,ite_false] at h0 h1 h2 h3 h4
    simp only [returnSteps,returnedState,returnEvents,Bool.false_eq_true,Wgmma.run,h0,h1,h2,h3,h4,Except.bind,ite_true,List.nil_append,List.cons_append,List.append_nil]

@[simp] theorem returnedState_status (s : Wgmma.State) (leader : Bool) :
    (returnedState s leader).base.scalar.core.thread.status = .done := by simp [returnedState]
@[simp] theorem returnedState_queries (s : Wgmma.State) (leader : Bool) :
    (returnedState s leader).base.scalar.core.queries = s.base.scalar.core.queries := by cases leader <;> rfl
@[simp] theorem returnedState_pending (s : Wgmma.State) (leader : Bool) :
    Wgmma.pending (returnedState s leader).ledger = Wgmma.pending s.ledger := by cases leader <;> rfl

theorem returnedState_complete (s : Wgmma.State) (leader : Bool) (hp : Wgmma.pending s.ledger = []) :
    Wgmma.Complete (returnedState s leader) := ⟨returnedState_status s leader,by simpa using hp⟩

end
end Ptx.Kernels.HopperDoubleBuffer
