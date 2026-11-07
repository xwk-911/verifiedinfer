import Ptx.Kernels.HopperDoubleBufferEntry

/-! Real barrier initialization, zero-tile guard, initial TMA issues and loop
register initialization. Producer election comes from entry_producer_flag;
barrier/TMA source events do not themselves establish graph admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def pathDirty (dirty : List String) (pcs : List Nat) : List String := pcs.foldl (fun names pc =>
  (((code[pc]?).map Wgmma.ordinaryNames).getD []++names).eraseDups) dirty

def initializedState (tiles : Nat) (lane : Wgmma.Lane) (leader : Bool) : Wgmma.State := {
  base := {scalar := {
    core := {thread := {pc := 33,regs := entryRegs tiles lane (if leader then 1 else 0)},generations := [(0,1)]}
    floats := HopperStage.zeroFloats
  }}
  ledger := {dirty := pathDirty (entryDirtyAt 28) (if leader then [28,29,30,31,32] else [28,32])}
}
def initializationEvents (leader : Bool) : List Wgmma.Event :=
  (if leader then [
    .base (.barrier ⟨⟨.shared .zero,0⟩,.init 1⟩),
    .base (.barrier ⟨⟨.shared .zero,8⟩,.init 1⟩),
    .base (.proxyFenceAsyncShared .zero)] else [])++
  [.base (.ampere (.ordinary (.barrierArrival 0 0))),.base (.ampere (.ordinary (.barrierReturn 0 0)))]
def initializationSteps (leader : Bool) : Nat := if leader then 5 else 2

theorem initialize_barriers (tiles : Nat) (lane : Wgmma.Lane) (leader : Bool) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code (initializationSteps leader)
      (entryState tiles lane (if leader then 1 else 0)) = .ok (initializedState tiles lane leader,initializationEvents leader) := by
  cases leader <;> rfl

def guardedInitialState (tiles : Nat) (lane : Wgmma.Lane) (leader : Bool) (zero : Bool) : Wgmma.State :=
  let s := initializedState tiles lane leader
  let test := Wgmma.integerAssign s (.setp .eq "%more" (.reg "%tiles") (.imm 0)) "%more" (if zero then 1 else 0)
  Wgmma.integerPC test (.branch "%more" true 85) (if zero then 85 else 35)

theorem initial_guard_execute (tiles : Nat) (lane : Wgmma.Lane) (leader : Bool) (hb : tiles ≤ 2^28) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code 2 (initializedState tiles lane leader) = .ok
      (guardedInitialState tiles lane leader (decide (tiles = 0)),[]) := by
  let s := initializedState tiles lane leader
  let test := Wgmma.integerAssign s (.setp .eq "%more" (.reg "%tiles") (.imm 0)) "%more" (if tiles = 0 then 1 else 0)
  have hw : wrap 32 tiles = tiles := Nat.mod_eq_of_lt (by omega)
  have h0 : Wgmma.step (ctx tiles lane) (oracle tiles) code s = .ok (test,[]) := by
    apply Wgmma.eq_zero_step rfl (by rfl) rfl _ (by omega)
    simp [Ptx.eval,s,initializedState,entryRegs,lookup,hw]
  have h1 : Wgmma.step (ctx tiles lane) (oracle tiles) code test = .ok
      (guardedInitialState tiles lane leader (decide (tiles = 0)),[]) := by
    have hs := Wgmma.branch_step (ctx := ctx tiles lane) (oracle := oracle tiles) (code := code)
      (s := test) (name := "%more") (positive := true) (target := 85)
      (value := if tiles = 0 then 1 else 0) rfl (by rfl) rfl (by simp [test])
    by_cases hz : tiles = 0 <;> simpa [guardedInitialState,test,s,hz,show (initializedState tiles lane leader).base.scalar.core.thread.pc = 33 from rfl] using hs
  dsimp only [s] at h0 h1
  simp only [Wgmma.run,h0,h1,Except.bind,List.nil_append]

def initialLoopRegs (tiles : Nat) (lane : Wgmma.Lane) (leader : Bool) : Bindings :=
  [("%phase1",0),("%phase0",0),("%slot",0),("%tile",0)]++
  (if leader then [("%copyb",2064),("%copya",16)] else [])++
  [("%more",0)]++entryRegs tiles lane (if leader then 1 else 0)
def initialLoopState (tiles : Nat) (lane : Wgmma.Lane) (leader : Bool) : Wgmma.State := {
  base := {scalar := {
    core := {thread := {pc := 45,regs := initialLoopRegs tiles lane leader},queries := if leader then 4 else 0,generations := [(0,1)]}
    floats := HopperStage.zeroFloats
  }}
  ledger := {dirty := pathDirty (initializedState tiles lane leader).ledger.dirty (if leader then [33,34,35,36,37,38,39,40,41,42,43,44] else [33,34,35,41,42,43,44])}
}
def initialCopies (tiles : Nat) (leader : Bool) : List Wgmma.Event :=
  if leader then [
    .base (.barrier ⟨⟨.shared .zero,0⟩,.arriveExpectTx 2304⟩),
    .base (.tmaIssue ⟨4096,aView 65536 tiles,⟨0,0⟩,16,0,0,HopperStage.aPayload (fun _ => 0)⟩),
    .base (.tmaIssue ⟨4224,bView 131072 tiles,⟨0,0⟩,2064,0,2,HopperStage.bPayload (fun _ => 0)⟩)] else []
def initialCopySteps (leader : Bool) : Nat := if leader then 10 else 5

theorem initial_copies_execute (tiles : Nat) (lane : Wgmma.Lane) (leader : Bool) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code (initialCopySteps leader)
      (guardedInitialState tiles lane leader false) = .ok (initialLoopState tiles lane leader,initialCopies tiles leader) := by
  cases leader <;> rfl

def initialSteps (leader : Bool) : Nat := 28+initializationSteps leader+2+initialCopySteps leader

theorem kernel_reaches_loop (tiles : Nat) (lane : Wgmma.Lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code (initialSteps (HopperStage.leader lane)) {} = .ok
      (initialLoopState tiles lane (HopperStage.leader lane),
       initializationEvents (HopperStage.leader lane)++initialCopies tiles (HopperStage.leader lane)) := by
  have hg := initial_guard_execute tiles lane (HopperStage.leader lane) hb
  simp only [show (tiles = 0) = False by simp [Nat.ne_of_gt ht],decide_false] at hg
  rw [initialSteps,Wgmma.run_add,Wgmma.run_add,Wgmma.run_add,entry_producer_flag]
  simp only [Except.bind,initialize_barriers,hg,initial_copies_execute,List.nil_append,List.append_nil]

end
end Ptx.Kernels.HopperDoubleBuffer
