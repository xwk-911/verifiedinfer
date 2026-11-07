import Ptx.Kernels.HopperDoubleBufferCompute
import Ptx.Hopper.WgmmaTmaSteps

/-! Actual PCs 65..72 select the buffer opposite the current MMA stage and
form the next A tile coordinate. Counter bounds retain unsigned PTX semantics;
source phase and election invariants are explicit, not memory-admission facts. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def prefetchAddressPrefix (s : Wgmma.State) (tile : Nat) : Wgmma.State :=
  let s1 := Wgmma.integerAssign s (.mov 64 "%nextbar" (.reg "%bar1")) "%nextbar" (8)
  let s2 := Wgmma.integerAssign s1 (.mov 64 "%copya" (.imm 2320)) "%copya" (2320)
  let s3 := Wgmma.integerAssign s2 (.mov 64 "%copyb" (.imm 4368)) "%copyb" (4368)
  Wgmma.integerPC s3 (.branch "%even" true 72) (if tile%2 = 0 then 72 else 69)

def prefetchSelected (s : Wgmma.State) (tile : Nat) : Wgmma.State :=
  if tile%2 = 0 then prefetchAddressPrefix s tile else
  let s4 := prefetchAddressPrefix s tile
  let s5 := Wgmma.integerAssign s4 (.mov 64 "%nextbar" (.reg "%bar0")) "%nextbar" (0)
  let s6 := Wgmma.integerAssign s5 (.mov 64 "%copya" (.imm 16)) "%copya" (16)
  Wgmma.integerAssign s6 (.mov 64 "%copyb" (.imm 2064)) "%copyb" (2064)

def prefetchAddressState (s : Wgmma.State) (tile next : Nat) : Wgmma.State :=
  Wgmma.integerAssign (prefetchSelected s tile) (.bin .mul 32 32 "%ay" (.reg "%next") (.imm 8)) "%ay" (next*8)
def prefetchAddressSteps (tile : Nat) : Nat := if tile%2 = 0 then 5 else 8

theorem prefetch_addresses_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State) (tile next : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 65)
    (hp : Wgmma.pending s.ledger = [])
    (he : lookup "%even" s.base.scalar.core.thread.regs = some (if tile%2 = 0 then 1 else 0))
    (hb0 : lookup "%bar0" s.base.scalar.core.thread.regs = some 0)
    (hb1 : lookup "%bar1" s.base.scalar.core.thread.regs = some 8)
    (hn : lookup "%next" s.base.scalar.core.thread.regs = some next)
    (hbound : next*8 < 2^32) :
    Wgmma.run ctx oracle code (prefetchAddressSteps tile) s = .ok (prefetchAddressState s tile next,[]) := by
  let s1 := Wgmma.integerAssign s (.mov 64 "%nextbar" (.reg "%bar1")) "%nextbar" (8)
  let s2 := Wgmma.integerAssign s1 (.mov 64 "%copya" (.imm 2320)) "%copya" (2320)
  let s3 := Wgmma.integerAssign s2 (.mov 64 "%copyb" (.imm 4368)) "%copyb" (4368)
  let s4 := Wgmma.integerPC s3 (.branch "%even" true 72) (if tile%2 = 0 then 72 else 69)
  have h1 : Wgmma.step ctx oracle code s = .ok (s1,[]) := by
    have hf : code[s.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 64 "%nextbar" (.reg "%bar1"))))) := by simp [s1,hpc,code,Generated.hopper_double_buffer_gemm.program]
    have hh := Wgmma.mov_step (value := 8) (ctx := ctx) (oracle := oracle) (by simp [s1,hr,hpc]) hf (by simpa [s1] using hp) (by simp [Ptx.eval,hb1])
    simpa only [s1,show wrap 64 8 = 8 from by decide] using hh
  have h2 : Wgmma.step ctx oracle code s1 = .ok (s2,[]) := by
    have hf : code[s1.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 64 "%copya" (.imm 2320))))) := by simp [s1,s2,hpc,code,Generated.hopper_double_buffer_gemm.program]
    have hh := Wgmma.mov_step (value := 2320) (ctx := ctx) (oracle := oracle) (by simp [s1,s2,hr,hpc]) hf (by simpa [s1,s2] using hp) (by rfl)
    simpa only [s2,show wrap 64 2320 = 2320 from by decide] using hh
  have h3 : Wgmma.step ctx oracle code s2 = .ok (s3,[]) := by
    have hf : code[s2.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 64 "%copyb" (.imm 4368))))) := by simp [s1,s2,s3,hpc,code,Generated.hopper_double_buffer_gemm.program]
    have hh := Wgmma.mov_step (value := 4368) (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,hr,hpc]) hf (by simpa [s1,s2,s3] using hp) (by rfl)
    simpa only [s3,show wrap 64 4368 = 4368 from by decide] using hh
  have h4 : Wgmma.step ctx oracle code s3 = .ok (s4,[]) := by
    have hf : code[s3.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.branch "%even" true 72)))) := by simp [s1,s2,s3,s4,hpc,code,Generated.hopper_double_buffer_gemm.program]
    have hh := Wgmma.branch_step (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,s4,hr,hpc]) hf (by simpa [s1,s2,s3,s4] using hp)
      (show lookup "%even" s3.base.scalar.core.thread.regs = some (if tile%2 = 0 then 1 else 0) by simpa [s1,s2,s3,s4] using he)
    by_cases ht : tile%2 = 0 <;> simpa [s1,s2,s3,s4,ht,hpc] using hh
  have hmul : Wgmma.step ctx oracle code (prefetchSelected s tile) = .ok (prefetchAddressState s tile next,[]) := by
    have hh : (prefetchSelected s tile).base.scalar.core.thread.pc = 72 := by by_cases h : tile%2 = 0 <;> simp [prefetchSelected,prefetchAddressPrefix,h]
    apply Wgmma.mul_const_step (by by_cases h : tile%2 = 0 <;> simpa [prefetchSelected,prefetchAddressPrefix,h] using hr)
      (by simp [hh,code,Generated.hopper_double_buffer_gemm.program])
      (by by_cases h : tile%2 = 0 <;> simpa [prefetchSelected,prefetchAddressPrefix,h] using hp)
      (by by_cases h : tile%2 = 0 <;> simpa [prefetchSelected,prefetchAddressPrefix,h] using hn) (by omega) (by decide) hbound
  by_cases ht : tile%2 = 0
  · dsimp only [s1,s2,s3,s4] at h1 h2 h3 h4
    simp only [ht,ite_true] at h1 h2 h3 h4
    simp only [prefetchSelected,ht,ite_true,prefetchAddressPrefix] at hmul
    simp only [prefetchAddressSteps,ht,ite_true,Wgmma.run,h1,h2,h3,h4,hmul,Except.bind,List.nil_append]
  ·
    let s5 := Wgmma.integerAssign s4 (.mov 64 "%nextbar" (.reg "%bar0")) "%nextbar" (0)
    let s6 := Wgmma.integerAssign s5 (.mov 64 "%copya" (.imm 16)) "%copya" (16)
    let s7 := Wgmma.integerAssign s6 (.mov 64 "%copyb" (.imm 2064)) "%copyb" (2064)
    have h5 : Wgmma.step ctx oracle code s4 = .ok (s5,[]) := by
      have hf : code[s4.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 64 "%nextbar" (.reg "%bar0"))))) := by simp [s1,s2,s3,s4,s5,ht,hpc,code,Generated.hopper_double_buffer_gemm.program]
      have hh := Wgmma.mov_step (value := 0) (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,s4,s5,hr,hpc,ht]) hf (by simpa [s1,s2,s3,s4,s5] using hp) (by simp [Ptx.eval,s1,s2,s3,s4,s5,hb0])
      simpa only [s5,show wrap 64 0 = 0 from by decide] using hh
    have h6 : Wgmma.step ctx oracle code s5 = .ok (s6,[]) := by
      have hf : code[s5.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 64 "%copya" (.imm 16))))) := by simp [s1,s2,s3,s4,s5,s6,ht,hpc,code,Generated.hopper_double_buffer_gemm.program]
      have hh := Wgmma.mov_step (value := 16) (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,s4,s5,s6,hr,hpc,ht]) hf (by simpa [s1,s2,s3,s4,s5,s6] using hp) (by rfl)
      simpa only [s6,show wrap 64 16 = 16 from by decide] using hh
    have h7 : Wgmma.step ctx oracle code s6 = .ok (s7,[]) := by
      have hf : code[s6.base.scalar.core.thread.pc]? = some (.ampere (.scalar (.integer (.mov 64 "%copyb" (.imm 2064))))) := by simp [s1,s2,s3,s4,s5,s6,s7,ht,hpc,code,Generated.hopper_double_buffer_gemm.program]
      have hh := Wgmma.mov_step (value := 2064) (ctx := ctx) (oracle := oracle) (by simp [s1,s2,s3,s4,s5,s6,s7,hr,hpc,ht]) hf (by simpa [s1,s2,s3,s4,s5,s6,s7] using hp) (by rfl)
      simpa only [s7,show wrap 64 2064 = 2064 from by decide] using hh
    dsimp only [s1,s2,s3,s4,s5,s6,s7] at h1 h2 h3 h4 h5 h6 h7
    simp only [ht,ite_false] at h1 h2 h3 h4 h5 h6 h7
    simp only [prefetchSelected,ht,ite_false,prefetchAddressPrefix] at hmul
    simp only [prefetchAddressSteps,ht,ite_false,Wgmma.run,h1,h2,h3,h4,h5,h6,h7,hmul,Except.bind,List.nil_append]

@[simp] theorem prefetchAddressState_pc (s : Wgmma.State) (tile next : Nat) :
    (prefetchAddressState s tile next).base.scalar.core.thread.pc = 73 := by
  by_cases h : tile%2 = 0 <;> simp [prefetchAddressState,prefetchSelected,prefetchAddressPrefix,h]
@[simp] theorem prefetchAddressState_status (s : Wgmma.State) (tile next : Nat) :
    (prefetchAddressState s tile next).base.scalar.core.thread.status = s.base.scalar.core.thread.status := by
  by_cases h : tile%2 = 0 <;> simp [prefetchAddressState,prefetchSelected,prefetchAddressPrefix,h]
@[simp] theorem prefetchAddressState_queries (s : Wgmma.State) (tile next : Nat) :
    (prefetchAddressState s tile next).base.scalar.core.queries = s.base.scalar.core.queries := by
  by_cases h : tile%2 = 0 <;> simp [prefetchAddressState,prefetchSelected,prefetchAddressPrefix,h]
@[simp] theorem prefetchAddressState_pending (s : Wgmma.State) (tile next : Nat) :
    Wgmma.pending (prefetchAddressState s tile next).ledger = Wgmma.pending s.ledger := by
  by_cases h : tile%2 = 0 <;> simp [prefetchAddressState,prefetchSelected,prefetchAddressPrefix,h]

theorem prefetchAddressState_operands (s : Wgmma.State) (tile next : Nat) :
    lookup "%nextbar" (prefetchAddressState s tile next).base.scalar.core.thread.regs = some (barrierAddress (stage (tile+1))) ∧
    lookup "%copya" (prefetchAddressState s tile next).base.scalar.core.thread.regs = some (aBase (stage (tile+1))) ∧
    lookup "%copyb" (prefetchAddressState s tile next).base.scalar.core.thread.regs = some (bBase (stage (tile+1))) ∧
    lookup "%ay" (prefetchAddressState s tile next).base.scalar.core.thread.regs = some (8*next) := by
  have hs : tile%2 = 0 ∨ tile%2 = 1 := by omega
  rcases hs with ht | ht
  all_goals have hn : (tile+1)%2 = 1-tile%2 := by omega
  all_goals simp [prefetchAddressState,prefetchSelected,prefetchAddressPrefix,ht,stage,hn,
    barrierAddress,aBase,bBase,Nat.mul_comm]

theorem prefetchAddressState_nat_frame (s : Wgmma.State) (tile next : Nat) (name : String)
    (hn : name ∉ ["%nextbar","%copya","%copyb","%ay"]) :
    lookup name (prefetchAddressState s tile next).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := by
  have hh : name ≠ "%nextbar" ∧ name ≠ "%copya" ∧ name ≠ "%copyb" ∧ name ≠ "%ay" := by simpa using hn
  by_cases h : tile%2 = 0 <;> simp [prefetchAddressState,prefetchSelected,prefetchAddressPrefix,h,hh]

theorem prefetchAddressState_float_frame (s : Wgmma.State) (tile next : Nat) (name : String)
    (hx : name ∉ ["%nextbar","%copya","%copyb","%ay"]) (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (prefetchAddressState s tile next).base.scalar.floats = declarationLookup name s.base.scalar.floats := by
  have hh : name ≠ "%nextbar" ∧ name ≠ "%copya" ∧ name ≠ "%copyb" ∧ name ≠ "%ay" := by simpa using hx
  by_cases h : tile%2 = 0
  all_goals simp only [prefetchAddressState,prefetchSelected,prefetchAddressPrefix,h,ite_true,ite_false,
    Wgmma.integerAssign,Wgmma.integerPC,Wgmma.ordinaryState,Ampere.intAssign,Ampere.intPC]
  all_goals simp [Scalar.intAssign_float,Scalar.intPC_float,hh,hn]

end
end Ptx.Kernels.HopperDoubleBuffer
