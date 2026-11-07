import Ptx.Kernels.HopperDoubleBufferKernelLoop
import Ptx.Kernels.HopperStageAddressValues
import Ptx.Hopper.WgmmaOutputSteps

/-! Actual PCs 85..91 on arbitrary completed-loop state. The existing address
layout lemmas are reused after connecting these translated instructions to
that layout. Float-bank availability is preserved through integer arithmetic.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def outputAddressState (s : Wgmma.State) (lane : Wgmma.Lane) : Wgmma.State :=
  let s1 := Wgmma.integerAssign s (.bin .mul 32 32 "%row" (.reg "%z") (.imm 16)) "%row" (HopperStage.rowFirst lane)
  let s2 := Wgmma.integerAssign s1 (.bin .add 32 32 "%row" (.reg "%row") (.reg "%y")) "%row" (HopperStage.rowFinal lane)
  let s3 := Wgmma.integerAssign s2 (.bin .mul 32 32 "%col" (.reg "%x") (.imm 2)) "%col" (HopperStage.colFinal lane)
  let s4 := Wgmma.integerAssign s3 (.bin .mul 32 32 "%linear" (.reg "%row") (.imm 8)) "%linear" (HopperStage.linearFirst lane)
  let s5 := Wgmma.integerAssign s4 (.bin .add 32 32 "%linear" (.reg "%linear") (.reg "%col")) "%linear" (HopperStage.linearFinal lane)
  let s6 := Wgmma.integerAssign s5 (.bin .mul 32 64 "%offset" (.reg "%linear") (.imm 4)) "%offset" (HopperStage.offsetFinal lane)
  Wgmma.integerAssign s6 (.bin .add 64 64 "%out" (.reg "%out") (.reg "%offset")) "%out" (HopperStage.outFinal lane)

theorem output_addresses_execute (context : Scalar.Context) (reply : Wgmma.Oracle) (s : Wgmma.State) (lane : Wgmma.Lane)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 85)
    (hp : Wgmma.pending s.ledger = [])
    (hx : lookup "%x" s.base.scalar.core.thread.regs = some (HopperStage.xWord lane))
    (hy : lookup "%y" s.base.scalar.core.thread.regs = some (HopperStage.yWord lane))
    (hz : lookup "%z" s.base.scalar.core.thread.regs = some (HopperStage.zWord lane))
    (hout : lookup "%out" s.base.scalar.core.thread.regs = some (wrap 64 8192)) :
    Wgmma.run context reply code 7 s = .ok (outputAddressState s lane,[]) := by
  let s1 := Wgmma.integerAssign s (.bin .mul 32 32 "%row" (.reg "%z") (.imm 16)) "%row" (HopperStage.rowFirst lane)
  let s2 := Wgmma.integerAssign s1 (.bin .add 32 32 "%row" (.reg "%row") (.reg "%y")) "%row" (HopperStage.rowFinal lane)
  let s3 := Wgmma.integerAssign s2 (.bin .mul 32 32 "%col" (.reg "%x") (.imm 2)) "%col" (HopperStage.colFinal lane)
  let s4 := Wgmma.integerAssign s3 (.bin .mul 32 32 "%linear" (.reg "%row") (.imm 8)) "%linear" (HopperStage.linearFirst lane)
  let s5 := Wgmma.integerAssign s4 (.bin .add 32 32 "%linear" (.reg "%linear") (.reg "%col")) "%linear" (HopperStage.linearFinal lane)
  let s6 := Wgmma.integerAssign s5 (.bin .mul 32 64 "%offset" (.reg "%linear") (.imm 4)) "%offset" (HopperStage.offsetFinal lane)
  let s7 := Wgmma.integerAssign s6 (.bin .add 64 64 "%out" (.reg "%out") (.reg "%offset")) "%out" (HopperStage.outFinal lane)
  have h1 : Wgmma.step context reply code s = .ok (s1,[]) := by
    apply Wgmma.integer_assign_step
      (by simp [s1,hr])
      (by simp [s1,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1] using hp) rfl (by intro bid he; cases he) rfl
    simp [localStep,Ptx.eval,s1,hx,hy,hz,hout,HopperStage.rowFirst,bind,Except.bind,pure,Except.pure,
      show wrap 32 16 = 16 from by decide,show wrap 32 8 = 8 from by decide,
      show wrap 32 4 = 4 from by decide,show wrap 32 2 = 2 from by decide]
  have h2 : Wgmma.step context reply code s1 = .ok (s2,[]) := by
    apply Wgmma.integer_assign_step
      (by simp [s1,s2,hr])
      (by simp [s1,s2,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1,s2] using hp) rfl (by intro bid he; cases he) rfl
    simp [localStep,Ptx.eval,s1,s2,hx,hy,hz,hout,HopperStage.rowFinal,bind,Except.bind,pure,Except.pure,
      show wrap 32 16 = 16 from by decide,show wrap 32 8 = 8 from by decide,
      show wrap 32 4 = 4 from by decide,show wrap 32 2 = 2 from by decide]
  have h3 : Wgmma.step context reply code s2 = .ok (s3,[]) := by
    apply Wgmma.integer_assign_step
      (by simp [s1,s2,s3,hr])
      (by simp [s1,s2,s3,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1,s2,s3] using hp) rfl (by intro bid he; cases he) rfl
    simp [localStep,Ptx.eval,s1,s2,s3,hx,hy,hz,hout,HopperStage.colFinal,bind,Except.bind,pure,Except.pure,
      show wrap 32 16 = 16 from by decide,show wrap 32 8 = 8 from by decide,
      show wrap 32 4 = 4 from by decide,show wrap 32 2 = 2 from by decide]
  have h4 : Wgmma.step context reply code s3 = .ok (s4,[]) := by
    apply Wgmma.integer_assign_step
      (by simp [s1,s2,s3,s4,hr])
      (by simp [s1,s2,s3,s4,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1,s2,s3,s4] using hp) rfl (by intro bid he; cases he) rfl
    simp [localStep,Ptx.eval,s1,s2,s3,s4,hx,hy,hz,hout,HopperStage.linearFirst,bind,Except.bind,pure,Except.pure,
      show wrap 32 16 = 16 from by decide,show wrap 32 8 = 8 from by decide,
      show wrap 32 4 = 4 from by decide,show wrap 32 2 = 2 from by decide]
  have h5 : Wgmma.step context reply code s4 = .ok (s5,[]) := by
    apply Wgmma.integer_assign_step
      (by simp [s1,s2,s3,s4,s5,hr])
      (by simp [s1,s2,s3,s4,s5,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1,s2,s3,s4,s5] using hp) rfl (by intro bid he; cases he) rfl
    simp [localStep,Ptx.eval,s1,s2,s3,s4,s5,hx,hy,hz,hout,HopperStage.linearFinal,bind,Except.bind,pure,Except.pure,
      show wrap 32 16 = 16 from by decide,show wrap 32 8 = 8 from by decide,
      show wrap 32 4 = 4 from by decide,show wrap 32 2 = 2 from by decide]
  have h6 : Wgmma.step context reply code s5 = .ok (s6,[]) := by
    apply Wgmma.integer_assign_step
      (by simp [s1,s2,s3,s4,s5,s6,hr])
      (by simp [s1,s2,s3,s4,s5,s6,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1,s2,s3,s4,s5,s6] using hp) rfl (by intro bid he; cases he) rfl
    simp [localStep,Ptx.eval,s1,s2,s3,s4,s5,s6,hx,hy,hz,hout,HopperStage.offsetFinal,bind,Except.bind,pure,Except.pure,
      show wrap 32 16 = 16 from by decide,show wrap 32 8 = 8 from by decide,
      show wrap 32 4 = 4 from by decide,show wrap 32 2 = 2 from by decide]
  have h7 : Wgmma.step context reply code s6 = .ok (s7,[]) := by
    apply Wgmma.integer_assign_step
      (by simp [s1,s2,s3,s4,s5,s6,s7,hr])
      (by simp [s1,s2,s3,s4,s5,s6,s7,hpc,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1,s2,s3,s4,s5,s6,s7] using hp) rfl (by intro bid he; cases he) rfl
    simp [localStep,Ptx.eval,s1,s2,s3,s4,s5,s6,s7,hx,hy,hz,hout,HopperStage.outFinal,bind,Except.bind,pure,Except.pure,
      show wrap 32 16 = 16 from by decide,show wrap 32 8 = 8 from by decide,
      show wrap 32 4 = 4 from by decide,show wrap 32 2 = 2 from by decide]
  dsimp only [s7,s6,s5,s4,s3,s2,s1] at h1 h2 h3 h4 h5 h6 h7
  simp only [Wgmma.run,h1,h2,h3,h4,h5,h6,h7,Except.bind,List.nil_append,outputAddressState]

@[simp] theorem outputAddressState_pc (s : Wgmma.State) (lane : Wgmma.Lane) (hpc : s.base.scalar.core.thread.pc = 85) :
    (outputAddressState s lane).base.scalar.core.thread.pc = 92 := by simp [outputAddressState,hpc]
@[simp] theorem outputAddressState_status (s : Wgmma.State) (lane : Wgmma.Lane) :
    (outputAddressState s lane).base.scalar.core.thread.status = s.base.scalar.core.thread.status := by simp [outputAddressState]
@[simp] theorem outputAddressState_queries (s : Wgmma.State) (lane : Wgmma.Lane) :
    (outputAddressState s lane).base.scalar.core.queries = s.base.scalar.core.queries := by simp [outputAddressState]
@[simp] theorem outputAddressState_pending (s : Wgmma.State) (lane : Wgmma.Lane) :
    Wgmma.pending (outputAddressState s lane).ledger = Wgmma.pending s.ledger := by simp [outputAddressState]
@[simp] theorem outputAddressState_out (s : Wgmma.State) (lane : Wgmma.Lane) :
    lookup "%out" (outputAddressState s lane).base.scalar.core.thread.regs = some (HopperStage.outFinal lane) := by simp [outputAddressState]

theorem outputAddressState_nat_frame (s : Wgmma.State) (lane : Wgmma.Lane) (name : String)
    (hn : name ∉ ["%row","%col","%linear","%offset","%out"]) :
    lookup name (outputAddressState s lane).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := by
  have hh : name ≠ "%row" ∧ name ≠ "%col" ∧ name ≠ "%linear" ∧ name ≠ "%offset" ∧ name ≠ "%out" := by simpa using hn
  simp [outputAddressState,hh]

theorem outputAddressState_float_frame (s : Wgmma.State) (lane : Wgmma.Lane) (name : String)
    (hx : name ∉ ["%row","%col","%linear","%offset","%out"]) (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (outputAddressState s lane).base.scalar.floats = declarationLookup name s.base.scalar.floats := by
  have hh : name ≠ "%row" ∧ name ≠ "%col" ∧ name ≠ "%linear" ∧ name ≠ "%offset" ∧ name ≠ "%out" := by simpa using hx
  simp only [outputAddressState,Wgmma.integerAssign,Wgmma.ordinaryState,Ampere.intAssign]
  simp [Scalar.intAssign_float,hh,hn]

theorem outputAddressState_accumulators (s : Wgmma.State) (lane : Wgmma.Lane) (values : Fin 4 → ℝ)
    (ha : Accumulators s values) : Accumulators (outputAddressState s lane) values := by
  intro i
  have hx : computeSlotName i ∉ ["%row","%col","%linear","%offset","%out"] := by fin_cases i <;> decide
  rw [outputAddressState_float_frame _ _ _ hx (ha i).2,outputAddressState_nat_frame _ _ _ hx]
  exact ha i

end
end Ptx.Kernels.HopperDoubleBuffer
