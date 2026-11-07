import Ptx.Kernels.HopperDoubleBufferDataEntry
import Ptx.Hopper.WgmmaTmaInversion

/-! Arbitrary-oracle initial TMA source execution. Finite completion derives
producer payload sizes. Consumers and the zero-tile guard do not constrain
unused TMA replies; descriptor/value/resource admission is separate. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def initialAInstruction : Hopper.Instr := .tmaLoad2D ⟨.reg "%copya",0⟩ (.reg "%mapa") (.imm 0) (.imm 0) ⟨.reg "%bar0",0⟩
def initialBInstruction : Hopper.Instr := .tmaLoad2D ⟨.reg "%copyb",0⟩ (.reg "%mapb") (.imm 0) (.imm 0) ⟨.reg "%bar0",0⟩
def initialAddressed (tiles : Nat) (lane : Wgmma.Lane) : Wgmma.State :=
  let s := Wgmma.integerPC (guardedInitialState tiles lane true false) (.branch "%leader" false 41) 36
  let a := Wgmma.integerAssign s (.mov 64 "%copya" (.imm 16)) "%copya" 16
  Wgmma.integerAssign a (.mov 64 "%copyb" (.imm 2064)) "%copyb" 2064
def initialArrived (tiles : Nat) (lane : Wgmma.Lane) : Wgmma.State :=
  Wgmma.advanceOrdinary (initialAddressed tiles lane) (.arriveExpectTx ⟨.reg "%bar0",0⟩ (.imm 2304))
def initialAIssued (tiles : Nat) (lane : Wgmma.Lane) : Wgmma.State := Wgmma.tmaState (initialArrived tiles lane) initialAInstruction
def initialBIssued (tiles : Nat) (lane : Wgmma.Lane) : Wgmma.State := Wgmma.tmaState (initialAIssued tiles lane) initialBInstruction
def replyInitialA (reply : Wgmma.Oracle) : TmaCopy := ⟨4096,reply.base.descriptor 0,⟨0,0⟩,16,0,0,reply.base.tmaBytes 1⟩
def replyInitialB (reply : Wgmma.Oracle) : TmaCopy := ⟨4224,reply.base.descriptor 2,⟨0,0⟩,2064,0,2,reply.base.tmaBytes 3⟩
def replyInitialCopies (reply : Wgmma.Oracle) (leader : Bool) : List Wgmma.Event :=
  if leader then [.base (.barrier ⟨⟨.shared .zero,0⟩,.arriveExpectTx 2304⟩),
    .base (.tmaIssue (replyInitialA reply)),.base (.tmaIssue (replyInitialB reply))] else []

theorem initial_arrival_any_reply (tiles lane) (reply : Wgmma.Oracle) :
    Wgmma.run (ctx tiles lane) reply code 4 (guardedInitialState tiles lane true false) =
      .ok (initialArrived tiles lane,[.base (.barrier ⟨⟨.shared .zero,0⟩,.arriveExpectTx 2304⟩)]) := by rfl

theorem initial_a_any_reply (tiles lane) (reply : Wgmma.Oracle)
    (ha : (reply.base.tmaBytes 1).length = (reply.base.descriptor 0).bytes) :
    Wgmma.step (ctx tiles lane) reply code (initialArrived tiles lane) =
      .ok (initialAIssued tiles lane,[.base (.tmaIssue (replyInitialA reply))]) := by
  have hs := Wgmma.tma_issue_step (ctx := ctx tiles lane) (oracle := reply) (s := initialArrived tiles lane)
    (dstAddr := 16) (descriptorAddr := 4096) (px := 0) (py := 0) (barrierAddr := 0)
    (by rfl) (show code[(initialArrived tiles lane).base.scalar.core.thread.pc]? = some initialAInstruction from rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) ha
  exact hs

theorem initial_b_any_reply (tiles lane) (reply : Wgmma.Oracle)
    (hb : (reply.base.tmaBytes 3).length = (reply.base.descriptor 2).bytes) :
    Wgmma.step (ctx tiles lane) reply code (initialAIssued tiles lane) =
      .ok (initialBIssued tiles lane,[.base (.tmaIssue (replyInitialB reply))]) := by
  exact Wgmma.tma_issue_step (ctx := ctx tiles lane) (oracle := reply) (s := initialAIssued tiles lane)
    (dstAddr := 2064) (descriptorAddr := 4224) (px := 0) (py := 0) (barrierAddr := 0)
    (by rfl) (show code[(initialAIssued tiles lane).base.scalar.core.thread.pc]? = some initialBInstruction from rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hb

theorem initial_a_prefix_any_reply (tiles lane) (reply : Wgmma.Oracle)
    (ha : (reply.base.tmaBytes 1).length = (reply.base.descriptor 0).bytes) :
    Wgmma.run (ctx tiles lane) reply code 5 (guardedInitialState tiles lane true false) =
      .ok (initialAIssued tiles lane,[.base (.barrier ⟨⟨.shared .zero,0⟩,.arriveExpectTx 2304⟩),.base (.tmaIssue (replyInitialA reply))]) := by
  rw [show 5 = 4+1 from rfl,Wgmma.run_add,initial_arrival_any_reply]
  simp only [Except.bind,Wgmma.run,initial_a_any_reply tiles lane reply ha,List.nil_append,List.cons_append,List.append_nil]

theorem completed_initial_payload_shapes {tiles lane reply count last events}
    (hn : Wgmma.run (ctx tiles lane) reply code count (guardedInitialState tiles lane true false) = .ok (last,events))
    (hd : last.base.scalar.core.thread.status = .done) :
    (reply.base.tmaBytes 1).length = (reply.base.descriptor 0).bytes ∧
      (reply.base.tmaBytes 3).length = (reply.base.descriptor 2).bytes := by
  have hp := initial_arrival_any_reply tiles lane reply
  have ha := Wgmma.completed_tma_shape_after_prefix hn hd hp (by rfl)
    (show code[(initialArrived tiles lane).base.scalar.core.thread.pc]? = some initialAInstruction from rfl)
  have hpA := initial_a_prefix_any_reply tiles lane reply ha
  have hb := Wgmma.completed_tma_shape_after_prefix hn hd hpA (by rfl)
    (show code[(initialAIssued tiles lane).base.scalar.core.thread.pc]? = some initialBInstruction from rfl)
  exact ⟨ha,hb⟩

theorem initial_copies_any_reply (tiles lane) (reply : Wgmma.Oracle) (leader : Bool)
    (hshape : leader = true → (reply.base.tmaBytes 1).length = (reply.base.descriptor 0).bytes ∧
      (reply.base.tmaBytes 3).length = (reply.base.descriptor 2).bytes) :
    Wgmma.run (ctx tiles lane) reply code (initialCopySteps leader) (guardedInitialState tiles lane leader false) =
      .ok (initialLoopState tiles lane leader,replyInitialCopies reply leader) := by
  cases leader with
  | false => rfl
  | true =>
    have hb := initial_b_any_reply tiles lane reply (hshape rfl).2
    have hb1 : Wgmma.run (ctx tiles lane) reply code 1 (initialAIssued tiles lane) =
        .ok (initialBIssued tiles lane,[.base (.tmaIssue (replyInitialB reply))]) := by
      simp only [Wgmma.run,hb,Except.bind,List.append_nil]
    have ht : Wgmma.run (ctx tiles lane) reply code 4 (initialBIssued tiles lane) = .ok (initialLoopState tiles lane true,[]) := by rfl
    change Wgmma.run (ctx tiles lane) reply code (5+(1+4)) _ = _
    rw [Wgmma.run_add,initial_a_prefix_any_reply tiles lane reply (hshape rfl).1]
    simp only [Except.bind]
    rw [Wgmma.run_add,hb1]
    simp only [Except.bind,ht,List.nil_append,List.cons_append,List.append_nil,replyInitialCopies,ite_true]

def guardSteps (leader : Bool) : Nat := 28+initializationSteps leader+2

theorem positive_guard_any_reply (tiles lane) (reply : Wgmma.Oracle) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Wgmma.run (ctx tiles lane) reply code (guardSteps (HopperStage.leader lane)) {} =
      .ok (guardedInitialState tiles lane (HopperStage.leader lane) false,initializationEvents (HopperStage.leader lane)) := by
  have hg := guard_any_reply tiles lane reply (HopperStage.leader lane) hb
  simp only [show (tiles = 0) = False by simp [Nat.ne_of_gt ht],decide_false] at hg
  rw [guardSteps,Wgmma.run_add,Wgmma.run_add,entry_any_reply]
  simp only [Except.bind,initialize_any_reply,hg,List.nil_append,List.append_nil]

theorem completed_kernel_initial_shapes {tiles lane reply count last events} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hn : Wgmma.run (ctx tiles lane) reply code count {} = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    HopperStage.leader lane = true → (reply.base.tmaBytes 1).length = (reply.base.descriptor 0).bytes ∧
      (reply.base.tmaBytes 3).length = (reply.base.descriptor 2).bytes := by
  intro hl
  have hprefix := positive_guard_any_reply tiles lane reply ht hb
  have hc := Wgmma.completed_after_running_prefix hn hd hprefix (by rfl)
  obtain ⟨tail,hsuffix,_⟩ := Wgmma.run_suffix_of_prefix (Nat.le_of_lt hc) hn hprefix
  rw [hl] at hsuffix
  exact completed_initial_payload_shapes hsuffix hd

theorem positive_initial_any_reply (tiles lane) (reply : Wgmma.Oracle) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hshape : HopperStage.leader lane = true → (reply.base.tmaBytes 1).length = (reply.base.descriptor 0).bytes ∧
      (reply.base.tmaBytes 3).length = (reply.base.descriptor 2).bytes) :
    Wgmma.run (ctx tiles lane) reply code (initialSteps (HopperStage.leader lane)) {} =
      .ok (initialLoopState tiles lane (HopperStage.leader lane),
        initializationEvents (HopperStage.leader lane)++replyInitialCopies reply (HopperStage.leader lane)) := by
  have hg := positive_guard_any_reply tiles lane reply ht hb
  have hcopy := initial_copies_any_reply tiles lane reply (HopperStage.leader lane) hshape
  change Wgmma.run (ctx tiles lane) reply code (guardSteps (HopperStage.leader lane)+initialCopySteps (HopperStage.leader lane)) {} = _
  rw [Wgmma.run_add,hg]
  simp only [Except.bind,hcopy]

end
end Ptx.Kernels.HopperDoubleBuffer
