import Ptx.Kernels.HopperDoubleBufferOutputAddresses

/-! Actual four f32 stores at PCs 92..95 with arbitrary available real values.
The emitted addresses reuse the checked 128-lane C layout; no source-heap or
observer correctness is inferred from these source events alone. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def outputStoreInstruction (i : Fin 4) : Hopper.Instr :=
  .ampere (.scalar (.store .f32 .global ⟨.reg "%out",HopperStage.storeOffset i⟩ (.reg (computeSlotName i))))
def outputWriteEvent (lane : Wgmma.Lane) (values : Fin 4 → ℝ) (i : Fin 4) : Wgmma.Event :=
  .base (.ampere (.ordinary (.write ⟨.global,wrap 64 (HopperStage.outFinal lane+HopperStage.storeOffset i)⟩
    (Symbolic.encode .f32 (values i)))))
def outputWriteEvents (lane : Wgmma.Lane) (values : Fin 4 → ℝ) : List Wgmma.Event :=
  [outputWriteEvent lane values 0,outputWriteEvent lane values 1,outputWriteEvent lane values 2,outputWriteEvent lane values 3]
def outputStored (s : Wgmma.State) : Wgmma.State :=
  let s1 := Wgmma.advanceOrdinary s (outputStoreInstruction 0)
  let s2 := Wgmma.advanceOrdinary s1 (outputStoreInstruction 1)
  let s3 := Wgmma.advanceOrdinary s2 (outputStoreInstruction 2)
  Wgmma.advanceOrdinary s3 (outputStoreInstruction 3)

theorem output_stores_execute (context : Scalar.Context) (reply : Wgmma.Oracle) (s : Wgmma.State)
    (lane : Wgmma.Lane) (values : Fin 4 → ℝ)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 92)
    (hp : Wgmma.pending s.ledger = [])
    (hout : lookup "%out" s.base.scalar.core.thread.regs = some (HopperStage.outFinal lane))
    (hacc : Accumulators s values) :
    Wgmma.run context reply code 4 s = .ok (outputStored s,outputWriteEvents lane values) := by
  let s1 := Wgmma.advanceOrdinary s (outputStoreInstruction 0)
  let s2 := Wgmma.advanceOrdinary s1 (outputStoreInstruction 1)
  let s3 := Wgmma.advanceOrdinary s2 (outputStoreInstruction 2)
  let s4 := Wgmma.advanceOrdinary s3 (outputStoreInstruction 3)
  have h1 : Wgmma.step context reply code s = .ok (s1,[outputWriteEvent lane values 0]) := by
    have hs := Wgmma.float_store_step (ctx := context) (oracle := reply) (code := code) (s := s)
      (format := .f32) (space := .global) (address := ⟨.reg "%out",HopperStage.storeOffset 0⟩) (value := .reg (computeSlotName 0))
      (addr := wrap 64 (HopperStage.outFinal lane+HopperStage.storeOffset 0)) (x := values 0)
      (by simp [s1,hr]) (by simp [s1,hpc,outputStoreInstruction,computeSlotName,HopperStage.storeOffset,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1] using hp)
      (by simp [evalAddr,Ptx.eval,s1,hout,bind,Except.bind,pure,Except.pure])
      (by simp [Scalar.eval,Scalar.require,s1,(hacc 0).1,bind,Except.bind,pure,Except.pure])
    simpa [s1,outputStoreInstruction,outputWriteEvent,Location.resolve] using hs
  have h2 : Wgmma.step context reply code s1 = .ok (s2,[outputWriteEvent lane values 1]) := by
    have hs := Wgmma.float_store_step (ctx := context) (oracle := reply) (code := code) (s := s1)
      (format := .f32) (space := .global) (address := ⟨.reg "%out",HopperStage.storeOffset 1⟩) (value := .reg (computeSlotName 1))
      (addr := wrap 64 (HopperStage.outFinal lane+HopperStage.storeOffset 1)) (x := values 1)
      (by simp [s1,s2,hr]) (by simp [s1,s2,hpc,outputStoreInstruction,computeSlotName,HopperStage.storeOffset,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1,s2] using hp)
      (by simp [evalAddr,Ptx.eval,s1,s2,hout,bind,Except.bind,pure,Except.pure])
      (by simp [Scalar.eval,Scalar.require,s1,s2,(hacc 1).1,bind,Except.bind,pure,Except.pure])
    simpa [s2,outputStoreInstruction,outputWriteEvent,Location.resolve] using hs
  have h3 : Wgmma.step context reply code s2 = .ok (s3,[outputWriteEvent lane values 2]) := by
    have hs := Wgmma.float_store_step (ctx := context) (oracle := reply) (code := code) (s := s2)
      (format := .f32) (space := .global) (address := ⟨.reg "%out",HopperStage.storeOffset 2⟩) (value := .reg (computeSlotName 2))
      (addr := wrap 64 (HopperStage.outFinal lane+HopperStage.storeOffset 2)) (x := values 2)
      (by simp [s1,s2,s3,hr]) (by simp [s1,s2,s3,hpc,outputStoreInstruction,computeSlotName,HopperStage.storeOffset,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1,s2,s3] using hp)
      (by simp [evalAddr,Ptx.eval,s1,s2,s3,hout,bind,Except.bind,pure,Except.pure])
      (by simp [Scalar.eval,Scalar.require,s1,s2,s3,(hacc 2).1,bind,Except.bind,pure,Except.pure])
    simpa [s3,outputStoreInstruction,outputWriteEvent,Location.resolve] using hs
  have h4 : Wgmma.step context reply code s3 = .ok (s4,[outputWriteEvent lane values 3]) := by
    have hs := Wgmma.float_store_step (ctx := context) (oracle := reply) (code := code) (s := s3)
      (format := .f32) (space := .global) (address := ⟨.reg "%out",HopperStage.storeOffset 3⟩) (value := .reg (computeSlotName 3))
      (addr := wrap 64 (HopperStage.outFinal lane+HopperStage.storeOffset 3)) (x := values 3)
      (by simp [s1,s2,s3,s4,hr]) (by simp [s1,s2,s3,s4,hpc,outputStoreInstruction,computeSlotName,HopperStage.storeOffset,code,Generated.hopper_double_buffer_gemm.program])
      (by simpa [s1,s2,s3,s4] using hp)
      (by simp [evalAddr,Ptx.eval,s1,s2,s3,s4,hout,bind,Except.bind,pure,Except.pure])
      (by simp [Scalar.eval,Scalar.require,s1,s2,s3,s4,(hacc 3).1,bind,Except.bind,pure,Except.pure])
    simpa [s4,outputStoreInstruction,outputWriteEvent,Location.resolve] using hs
  dsimp only [s4,s3,s2,s1] at h1 h2 h3 h4
  simp only [Wgmma.run,h1,h2,h3,h4,Except.bind,List.nil_append,List.cons_append,List.append_nil,outputStored,outputWriteEvents]

@[simp] theorem outputStored_pc (s : Wgmma.State) :
    (outputStored s).base.scalar.core.thread.pc = s.base.scalar.core.thread.pc+4 := rfl
@[simp] theorem outputStored_status (s : Wgmma.State) :
    (outputStored s).base.scalar.core.thread.status = s.base.scalar.core.thread.status := rfl
@[simp] theorem outputStored_queries (s : Wgmma.State) :
    (outputStored s).base.scalar.core.queries = s.base.scalar.core.queries := rfl
@[simp] theorem outputStored_pending (s : Wgmma.State) :
    Wgmma.pending (outputStored s).ledger = Wgmma.pending s.ledger := rfl
@[simp] theorem outputStored_nat (s : Wgmma.State) (name : String) :
    lookup name (outputStored s).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := rfl
@[simp] theorem outputStored_float (s : Wgmma.State) (name : String) :
    declarationLookup name (outputStored s).base.scalar.floats = declarationLookup name s.base.scalar.floats := rfl

theorem output_write_address (lane : Wgmma.Lane) (i : Fin 4) :
    wrap 64 (HopperStage.outFinal lane+HopperStage.storeOffset i) =
      8192+4*(8*(Wgmma.cCoord (lane,i)).1.val+(Wgmma.cCoord (lane,i)).2.val) :=
  HopperStage.actual_output_address lane i

theorem output_write_bounds (lane : Wgmma.Lane) (i : Fin 4) :
    8192 ≤ wrap 64 (HopperStage.outFinal lane+HopperStage.storeOffset i) ∧
    wrap 64 (HopperStage.outFinal lane+HopperStage.storeOffset i)+4 ≤ 10240 :=
  HopperStage.actual_output_bounds lane i

end
end Ptx.Kernels.HopperDoubleBuffer
