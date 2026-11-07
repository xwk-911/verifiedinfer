import Ptx.ISA.TypedSemantics
import Ptx.Generated.Copy
import Ptx.Generated.SharedSwap
import Ptx.Generated.Loop
import Ptx.Generated.MissingSync
import Ptx.Generated.OutOfBounds
import Ptx.Generated.BarrierPublish

/-! Independent Lean validation rejects corrupt metadata/instructions even if
Rust emits them. Initialization, safety and termination remain separate duties.
-/
namespace Ptx.TypingTests
open Ptx.ISA

def registers : RegisterDeclarations := [
  ("%r",.u32),("%b",.b32),("%d",.u64),("%bits64",.b64),("%p",.pred)]
def parameters : ParameterDeclarations := [("ptr",64),("n",32)]

theorem generated_copy_typed : ProgramTyped Generated.copy.registerDeclarations Generated.copy.parameters Generated.copy.program :=
  Generated.copy.checked.valid
theorem generated_shared_typed : ProgramTyped Generated.shared_swap.registerDeclarations Generated.shared_swap.parameters Generated.shared_swap.program :=
  Generated.shared_swap.checked.valid
theorem generated_loop_typed : ProgramTyped Generated.loop.registerDeclarations Generated.loop.parameters Generated.loop.program :=
  Generated.loop.checked.valid
theorem generated_missing_sync_typed : ProgramTyped Generated.missing_sync.registerDeclarations Generated.missing_sync.parameters Generated.missing_sync.program :=
  Generated.missing_sync.checked.valid
theorem generated_out_of_bounds_typed : ProgramTyped Generated.out_of_bounds.registerDeclarations Generated.out_of_bounds.parameters Generated.out_of_bounds.program :=
  Generated.out_of_bounds.checked.valid
theorem generated_publication_typed : ProgramTyped Generated.barrier_publish.registerDeclarations Generated.barrier_publish.parameters Generated.barrier_publish.program :=
  Generated.barrier_publish.checked.valid

theorem malformed_instructions_rejected :
    ¬ InstructionTyped registers parameters 2 (.mov 32 "%p" (.imm 0)) ∧
    ¬ InstructionTyped registers parameters 2 (.load .global "%r" {base := .reg "%r"}) ∧
    ¬ InstructionTyped registers parameters 2 (.bin .mul 32 64 "%r" (.reg "%b") (.imm 4)) ∧
    ¬ InstructionTyped registers parameters 2 (.mov 33 "%r" (.imm 1)) ∧
    ¬ InstructionTyped registers parameters 2 (.param 64 "%d" "n") ∧
    ¬ InstructionTyped registers parameters 2 (.jump 2) ∧
    ¬ InstructionTyped registers parameters 2 (.barrier 16) ∧
    ¬ InstructionTyped registers parameters 2 (.mov 32 "%r" (.imm 4294967296)) ∧
    ¬ InstructionTyped registers parameters 2 (.mov 64 "%d" .tid) := by decide

theorem duplicate_declarations_rejected :
    ¬ ProgramTyped [("%r",.u32),("%r",.u64)] [] [.ret] ∧
    ¬ ProgramTyped [] [("x",32),("x",64)] [.ret] ∧
    ¬ ProgramTyped [] [("x",33)] [.ret] := by decide

def bitProgram : CheckedProgram := {
  registers := registers
  parameters := parameters
  code := [.mov 32 "%b" (.imm 4294967295),.bin .mul 32 64 "%bits64" (.reg "%b") (.imm 4),
    .bin .add 64 64 "%d" (.reg "%bits64") (.imm 1),.setp .eq "%p" (.reg "%b") (.imm 0),
    .branch "%p" true 6,.mov 32 "%r" (.imm 7),.ret]
  valid := by decide
}
def ctx : Event.Context := ⟨⟨.zero,.zero⟩,[]⟩
def bitResult := bitProgram.eventRun ctx (fun _ => 0) 7 {}

theorem mixed_register_execution :
    bitResult.toOption.map (fun result => (lookup "%d" result.1.thread.regs,lookup "%r" result.1.thread.regs,
      lookup "%p" result.1.thread.regs,result.1.thread.status)) = some (some 17179869181,some 7,some 0,.done) := by decide

theorem mixed_register_execution_typed :
    ∃ final events, bitResult = .ok (final,events) ∧ RegistersTyped bitProgram.registers final.thread.regs := by
  let result := bitResult.toOption.getD ({},[])
  have hr : bitResult = .ok result := by decide
  refine ⟨result.1,result.2,hr,?_⟩
  have hs : Event.run ctx (fun _ => 0) bitProgram.code 7 {} = .ok result := by
    simpa only [bitResult,bitProgram.event_run_erases] using hr
  exact event_run_preserves_types bitProgram hs (registers_empty _)

def uninitialized : CheckedProgram := {
  registers := registers,parameters := [],code := [.mov 32 "%r" (.reg "%b"),.ret],valid := by decide
}

theorem typing_does_not_initialize :
    Event.step ctx (fun _ => 0) uninitialized.code {} = .error (.register "%b") := by decide

def forever : CheckedProgram := {registers := [],parameters := [],code := [.jump 0],valid := by decide}

theorem typing_does_not_terminate (n : Nat) : Event.run ctx (fun _ => 0) forever.code n {} = .ok ({},[]) := by
  have hs : Event.step ctx (fun _ => 0) forever.code {} = .ok ({},[]) := by decide
  induction n with
  | zero => rfl
  | succ n ih => simp only [Event.run,hs,Except.bind,ih,List.nil_append]

end Ptx.TypingTests
