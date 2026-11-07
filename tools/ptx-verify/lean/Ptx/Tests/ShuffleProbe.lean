import Ptx.Kernels.ShuffleProbeFrame
import Ptx.Kernels.ShuffleProbeValues

/-! Real generated exported probes: both control paths, 3-D numbering, u32/u64
wrapping, original/ordinary event indices and arbitrary local oracle replies.
These tests do not replace launch-wide definedness/memory/observer witnesses. -/
namespace Ptx.ShuffleProbeTests
open Ptx.ISA Ptx.Shuffle
open Ptx.Kernels.ShuffleProbe
noncomputable section

def bindings (input : Inputs) : Bindings :=
  [("Out",input.out),("B",input.b),("C",input.c),("Mask",input.mask),("Base",input.base)]
theorem all_parameter_bindings (input : Inputs) : Params input (bindings input) := by constructor <;> rfl
def input : Inputs := ⟨4096,1,31,0xffffffff,0xfffffff0⟩
def ctx : Scalar.Context := {id := ⟨.zero,⟨3,2,1⟩⟩,block := ⟨4,4,4⟩,params := bindings input}
def answers (value : Nat) (predicate : Bool) : Shuffle.Oracle :=
  ⟨fun query => .integer (999+query),fun query => if query = 0 then (value,predicate) else (4294967303+query,!predicate)⟩
def trace (mode : Mode) (value : Nat) (predicate : Bool) : Shuffle.ThreadTrace :=
  ⟨ctx.id,answers value predicate,24,finalState mode input ctx value predicate,events mode input ctx value predicate⟩

theorem all_modes_equal_generated_programs :
    code .up = Generated.shuffle_up.program ∧ code .down = Generated.shuffle_down.program ∧
    code .bfly = Generated.shuffle_bfly.program ∧ code .idx = Generated.shuffle_idx.program := ⟨rfl,rfl,rfl,rfl⟩

theorem all_modes_are_mechanically_typed (mode : Mode) : Shuffle.ProgramTyped 70
    Generated.shuffle_up.registerDeclarations Generated.shuffle_up.parameters (code mode) := mechanically_typed mode

theorem all_modes_and_predicates_have_actual_source_runs (mode : Mode) (value : Nat) (predicate : Bool) :
    Produced (code mode) (bindings input) ctx.block (trace mode value predicate) :=
  complete_source_run mode input ctx (answers value predicate) (all_parameter_bindings input)

theorem complete_count_is_derived {mode value predicate n state emitted}
    (hr : Shuffle.run ctx (answers value predicate) (code mode) n {} = .ok (state,emitted))
    (hd : state.base.core.thread.status = .done) : n = 24 :=
  (completed_source_shape (all_parameter_bindings input) hr hd).1

theorem both_branches_return_at_the_same_source_pc (mode : Mode) (value : Nat) (predicate : Bool) :
    (finalState mode input ctx value predicate).base.core.thread.pc = 24 ∧
    (finalState mode input ctx value predicate).base.core.thread.status = .done := by
  cases predicate <;> exact ⟨rfl,rfl⟩

theorem three_dimensional_index_uses_all_coordinates : rawIndex ctx = 27 := by decide
theorem source_input_uses_u32_wrap : inputWord input ctx = 11 := by decide
theorem output_address_uses_eight_bytes_per_thread : address input ctx = 4312 := by decide
theorem second_export_is_four_bytes_after_the_first : outputLoc input ctx 4 = ⟨.global,4316⟩ := by decide

theorem word_replies_are_wrapped_before_export (mode : Mode) (predicate : Bool) :
    events mode input ctx 4294967313 predicate = events mode input ctx 17 predicate := by
  cases predicate <;> rfl

theorem exactly_one_shuffle_query_and_no_memory_queries (mode : Mode) (value : Nat) (predicate : Bool) :
    (finalState mode input ctx value predicate).queries = 1 ∧
    (finalState mode input ctx value predicate).base.core.queries = 0 := by
  cases predicate <;> exact ⟨rfl,rfl⟩

theorem original_trace_has_three_events (mode : Mode) (value : Nat) (predicate : Bool) :
    (events mode input ctx value predicate).length = 3 := rfl
theorem ordinary_view_has_two_events (mode : Mode) (value : Nat) (predicate : Bool) :
    (ordinaryEvents (events mode input ctx value predicate)).length = 2 := rfl

def flagBytes (predicate : Bool) : List Nat :=
  match ((outputEvents input ctx 17 predicate)[1]? : Option Shuffle.Kind) with
  | some (.ordinary (.write _ bytes)) => bytes.map (fun value => match value with | .bits bits => bits.toNat | _ => 999999)
  | _ => []

theorem false_predicate_really_exports_zero : flagBytes false = [0,0,0,0] := by decide
theorem true_predicate_really_exports_one : flagBytes true = [1,0,0,0] := by decide

def wrappingInput : Inputs := {input with out := 2^64-8}
def wrappingContext : Scalar.Context := {ctx with id := ⟨.zero,⟨63,0,0⟩⟩,block := ⟨64,1,1⟩,params := bindings wrappingInput}

theorem raw_source_address_does_not_assume_no_overflow : address wrappingInput wrappingContext = 496 := by decide
theorem wrapping_source_still_needs_separate_allocation_obligations (mode : Mode) :
    Shuffle.run wrappingContext (answers 7 true) (code mode) 24 {} =
      .ok (finalState mode wrappingInput wrappingContext 7 true,events mode wrappingInput wrappingContext 7 true) :=
  complete_source_run mode wrappingInput wrappingContext (answers 7 true) (all_parameter_bindings wrappingInput)

theorem padding_after_source_completion_faults (mode : Mode) (value : Nat) (predicate : Bool) :
    Shuffle.run ctx (answers value predicate) (code mode) 25 {} = .error (.integer .blocked) := by
  rw [show 25 = 24+1 from rfl,Shuffle.run_add,complete_source_run mode input ctx _ (all_parameter_bindings input)]
  simp [answers,Except.bind,Except.map,Shuffle.run_done_suffix (show (finalState mode input ctx value predicate).base.core.thread.status = .done from rfl) 0]

theorem emitted_and_memory_serials_are_different (mode : Mode) (value : Nat) (predicate : Bool) :
    (events mode input ctx value predicate)[0]? = some (.shuffle (record mode input ctx value predicate)) ∧
    (ordinaryEvents (events mode input ctx value predicate))[0]? =
      some (.write (outputLoc input ctx 0) ((encodeU32 (w32 value)).map Symbolic.Byte.bits)) := ⟨rfl,rfl⟩

def crossingInput : Inputs := {input with out := 2^64-4}
def crossingContext : Scalar.Context := {ctx with id := ⟨.zero,.zero⟩,block := .one,params := bindings crossingInput}
def crossingLaunch : Scalar.Launch := ⟨⟨.one,.one⟩,bindings crossingInput,fun _ => .bits (byte 99)⟩

theorem aligned_flag_address_can_wrap_to_zero :
    crossingInput.out % 4 = 0 ∧ outputLoc crossingInput crossingContext 4 = ⟨.global,0⟩ := by decide

theorem wrapped_flag_is_in_the_actual_output_footprint :
    OutputFootprint crossingInput crossingLaunch ⟨.global,0⟩ := by
  refine ⟨⟨.zero,.zero⟩,?_,4,Or.inr rfl,rfl,?_,?_⟩
  · simp [crossingLaunch,ThreadId.Valid,Dim3.Within,Dim3.zero,Dim3.one]
  · decide
  · decide

theorem misaligned_output_does_not_gain_alignment_from_wrapping :
    (outputLoc {input with out := 4097} ctx 0).address % 4 = 1 := by decide

theorem independent_values_for_all_four_modes :
    expectedWord .up input ctx = 11 ∧ expectedPredicate .up input ctx = false ∧
    expectedWord .down input ctx = 12 ∧ expectedPredicate .down input ctx = true ∧
    expectedWord .bfly input ctx = 10 ∧ expectedPredicate .bfly input ctx = true ∧
    expectedWord .idx input ctx = 4294967281 ∧ expectedPredicate .idx input ctx = true := by decide

def secondWarpContext : Scalar.Context := {ctx with id := ⟨.zero,⟨63,0,0⟩⟩,block := ⟨64,1,1⟩}
theorem selected_value_keeps_the_warp_offset : expectedWord .bfly input secondWarpContext = 46 := by decide

theorem modular_index_interpretation_handles_large_dimensions :
    rawIndex {ctx with block := ⟨4294967297,4294967298,1⟩} =
      w32 (linear ⟨4294967297,4294967298,1⟩ ctx.id) := raw_index_is_linear_mod_u32 _

end
end Ptx.ShuffleProbeTests
