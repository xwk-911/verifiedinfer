import Ptx.Kernels.HopperDoubleBufferInitialization
import Ptx.Kernels.HopperDoubleBufferDataOracle

/-! The real pre-query entry is independent of the oracle; initial TMA copies
then capture arbitrary tile-zero payloads. These are source construction facts,
not descriptor/input-memory agreement or resource admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

theorem entry_twelve_any_reply (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) :
    Wgmma.run (ctx tiles lane) reply code 12 {} = .ok (entryPartial 12 4 tiles lane (HopperStage.leaderWord lane),[]) := by rfl

theorem descriptor_a0_any_reply (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (flag : Nat) :
    Wgmma.run (ctx tiles lane) reply code 3 (entryPartial 12 4 tiles lane flag) = .ok (entryPartial 15 3 tiles lane flag,[]) := by rfl

theorem descriptor_b0_any_reply (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (flag : Nat) :
    Wgmma.run (ctx tiles lane) reply code 3 (entryPartial 15 3 tiles lane flag) = .ok (entryPartial 18 2 tiles lane flag,[]) := by rfl

theorem descriptor_a1_any_reply (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (flag : Nat) :
    Wgmma.run (ctx tiles lane) reply code 3 (entryPartial 18 2 tiles lane flag) = .ok (entryPartial 21 1 tiles lane flag,[]) := by rfl

theorem descriptor_b1_any_reply (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (flag : Nat) :
    Wgmma.run (ctx tiles lane) reply code 3 (entryPartial 21 1 tiles lane flag) = .ok (entryPartial 24 0 tiles lane flag,[]) := by rfl

theorem entry_zero_any_reply (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (flag : Nat) :
    Wgmma.run (ctx tiles lane) reply code 4 (entryPartial 24 0 tiles lane flag) = .ok (entryState tiles lane flag,[]) := by rfl

theorem entry_any_reply (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) :
    Wgmma.run (ctx tiles lane) reply code 28 {} = .ok (entryState tiles lane (if HopperStage.leader lane then 1 else 0),[]) := by
  rw [show 28 = 12+3+3+3+3+4 from rfl,Wgmma.run_add,Wgmma.run_add,Wgmma.run_add,Wgmma.run_add,Wgmma.run_add,entry_twelve_any_reply]
  simp only [Except.bind,descriptor_a0_any_reply,descriptor_b0_any_reply,descriptor_a1_any_reply,descriptor_b1_any_reply,
    entry_zero_any_reply,List.nil_append,HopperStage.leader_word_value]

theorem initialize_any_reply (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (leader : Bool) :
    Wgmma.run (ctx tiles lane) reply code (initializationSteps leader) (entryState tiles lane (if leader then 1 else 0)) =
      .ok (initializedState tiles lane leader,initializationEvents leader) := by cases leader <;> rfl

theorem guard_any_reply (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (leader : Bool) (hb : tiles ≤ 2^28) :
    Wgmma.run (ctx tiles lane) reply code 2 (initializedState tiles lane leader) =
      .ok (guardedInitialState tiles lane leader (decide (tiles = 0)),[]) := by
  let s := initializedState tiles lane leader
  let test := Wgmma.integerAssign s (.setp .eq "%more" (.reg "%tiles") (.imm 0)) "%more" (if tiles = 0 then 1 else 0)
  have hw : wrap 32 tiles = tiles := Nat.mod_eq_of_lt (by omega)
  have h0 : Wgmma.step (ctx tiles lane) reply code s = .ok (test,[]) := by
    apply Wgmma.eq_zero_step rfl (by rfl) rfl _ (by omega)
    simp [Ptx.eval,s,initializedState,entryRegs,lookup,hw]
  have h1 : Wgmma.step (ctx tiles lane) reply code test = .ok (guardedInitialState tiles lane leader (decide (tiles = 0)),[]) := by
    have hs := Wgmma.branch_step (ctx := ctx tiles lane) (oracle := reply) (code := code)
      (s := test) (name := "%more") (positive := true) (target := 85) (value := if tiles = 0 then 1 else 0)
      rfl (by rfl) rfl (by simp [test])
    by_cases hz : tiles = 0 <;> simpa [guardedInitialState,test,s,hz,show (initializedState tiles lane leader).base.scalar.core.thread.pc = 33 from rfl] using hs
  dsimp only [s] at h0 h1
  simp only [Wgmma.run,h0,h1,Except.bind,List.nil_append]

def dataInitialCopies (a : TileA) (b : TileB) (tiles : Nat) (leader : Bool) : List Wgmma.Event :=
  if leader then [
    .base (.barrier ⟨⟨.shared .zero,0⟩,.arriveExpectTx 2304⟩),
    .base (.tmaIssue ⟨4096,aView 65536 tiles,⟨0,0⟩,16,0,0,HopperStage.aPayload (a 0)⟩),
    .base (.tmaIssue ⟨4224,bView (dataBBase tiles) tiles,⟨0,0⟩,2064,0,2,HopperStage.bPayload (b 0)⟩)] else []

theorem data_initial_copies (a b tiles lane) (leader : Bool) :
    Wgmma.run (ctx tiles lane) (dataOracle a b tiles lane) code (initialCopySteps leader)
      (guardedInitialState tiles lane leader false) = .ok (initialLoopState tiles lane leader,dataInitialCopies a b tiles leader) := by
  cases leader <;> rfl

theorem data_kernel_reaches_loop (a b tiles lane) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Wgmma.run (ctx tiles lane) (dataOracle a b tiles lane) code (initialSteps (HopperStage.leader lane)) {} =
      .ok (initialLoopState tiles lane (HopperStage.leader lane),
        initializationEvents (HopperStage.leader lane)++dataInitialCopies a b tiles (HopperStage.leader lane)) := by
  have hg := guard_any_reply tiles lane (dataOracle a b tiles lane) (HopperStage.leader lane) hb
  simp only [show (tiles = 0) = False by simp [Nat.ne_of_gt ht],decide_false] at hg
  rw [initialSteps,Wgmma.run_add,Wgmma.run_add,Wgmma.run_add,entry_any_reply]
  simp only [Except.bind,initialize_any_reply,hg,data_initial_copies,List.nil_append,List.append_nil]

end
end Ptx.Kernels.HopperDoubleBuffer
