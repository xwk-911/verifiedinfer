import Ptx.Kernels.HopperDoubleBufferDataTensor
import Ptx.Tests.HopperDoubleBuffer

/-! Nonuniform real-data source witness tests. Numeric symbolic byte facts use
proved source/spec correspondence, never a real-valued-state equality decider.
Memory/resource admission and hardware bit equality remain distinct obligations.
-/
namespace Ptx.HopperDoubleBufferDataTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

abbrev a := Ptx.HopperDoubleBufferTests.nonuniformA
abbrev b := Ptx.HopperDoubleBufferTests.nonuniformB

def source (tiles : Nat) (lane : Wgmma.Lane) :=
  (Wgmma.run (ctx tiles lane) (dataOracle a b tiles lane) code (completeSteps tiles lane) {}).toOption
structure Metadata where
  pc : Nat
  query : Nat
  groups : Nat
  completed : Nat
  pending : Nat
  calls : Nat
  done : Bool
  deriving DecidableEq

def metadata (tiles : Nat) (lane : Wgmma.Lane) : Option Metadata :=
  (source tiles lane).map fun r => ⟨r.1.base.scalar.core.thread.pc,r.1.base.scalar.core.queries,r.1.ledger.groups,
    r.1.ledger.completed,(Wgmma.pending r.1.ledger).length,r.1.ledger.calls.length,r.1.base.scalar.core.thread.status == .done⟩
def rawWrite (tiles : Nat) (lane : Wgmma.Lane) (index : Nat) : Option (Option (Nat × List Symbolic.Byte)) :=
  (source tiles lane).map fun r => (r.2.filterMap globalWrite)[index]?
def transferMetadata : Wgmma.Event → Option (Nat × Nat × Nat) :=
  fun event => match event with
  | .base (.tmaIssue copy) => some (copy.descriptor.base,copy.destination,copy.queryBase)
  | _ => none
def transfers (tiles : Nat) (lane : Wgmma.Lane) := (source tiles lane).map fun r => r.2.filterMap transferMetadata

theorem nonuniform_producer_returns : metadata 3 0 = some ⟨100,21,3,3,0,3,true⟩ := by decide
theorem nonuniform_peer_returns : metadata 3 127 = some ⟨100,9,3,3,0,3,true⟩ := by decide
theorem nonuniform_zero_tiles_return : metadata 0 0 = some ⟨100,0,0,0,0,0,true⟩ := by decide
theorem nonuniform_tma_origins : transfers 3 0 = some [(65536,16,0),(71680,2064,2),(65536,2320,5),(71680,4368,7),(65536,16,12),(71680,2064,14)] := by decide

theorem first_output_value : ((dataCompleteEvents a b 3 0).filterMap globalWrite)[0]? = some (8192,Symbolic.encode .f32 20) := by
  rw [data_complete_write_specification]
  change some (8192,Symbolic.encode .f32 (specification a b 3 (0,0))) = _
  have hv : specification a b 3 (0,0) = 20 :=
    (result_matches_specification a b 3 (0,0)).symm.trans Ptx.HopperDoubleBufferTests.nonuniform_first_three_tiles
  rw [hv]

theorem last_output_value : ((dataCompleteEvents a b 3 127).filterMap globalWrite)[3]? = some (10236,Symbolic.encode .f32 29440) := by
  rw [data_complete_write_specification]
  change some (10236,Symbolic.encode .f32 (specification a b 3 (63,7))) = _
  have hv : specification a b 3 (63,7) = 29440 :=
    (result_matches_specification a b 3 (63,7)).symm.trans Ptx.HopperDoubleBufferTests.nonuniform_last_three_tiles
  rw [hv]

theorem actual_first_output : rawWrite 3 0 0 = some (some (8192,Symbolic.encode .f32 20)) := by
  rw [rawWrite,source,data_complete_run a b 3 0 (by decide)]
  simp only [Except.toOption,Option.map_some,first_output_value]

theorem actual_last_output : rawWrite 3 127 3 = some (some (10236,Symbolic.encode .f32 29440)) := by
  rw [rawWrite,source,data_complete_run a b 3 127 (by decide)]
  simp only [Except.toOption,Option.map_some,last_output_value]

theorem final_call_output : (dataIterationCall a b 3 2 0).output 0 = 20 := by
  rw [data_call_output a b 3 2 0 (by decide)]
  exact Ptx.HopperDoubleBufferTests.nonuniform_first_three_tiles

theorem final_call_input : (dataIterationCall a b 3 2 0).input 0 = 8 := by
  rw [data_call_input a b 3 2 0 (by decide)]
  norm_num [result,Wgmma.matrixStep,Wgmma.cCoord,a,b,Ptx.HopperDoubleBufferTests.nonuniformA,Ptx.HopperDoubleBufferTests.nonuniformB,Fin.sum_univ_succ]

theorem zero_final_reply_rejected : ¬Wgmma.Arithmetic (a 2) (b 2)
    (fun p => (dataIterationCall a b 3 2 p.1).input p.2) (fun _ => 0) := by
  intro h
  have hg := data_calls_arithmetic a b 3 2 (by decide) (0,0)
  have hb := h (0,0)
  have he : (0 : ℝ) = 20 := hb.trans hg.symm |>.trans final_call_output
  norm_num at he

theorem native_query_indices : nativeTile 3 true 9 = 0 ∧ nativeTile 3 true 16 = 1 ∧ nativeTile 3 true 19 = 2 := by decide
theorem consumer_query_indices : nativeTile 3 false 1 = 0 ∧ nativeTile 3 false 4 = 1 ∧ nativeTile 3 false 7 = 2 := by decide
theorem large_input_regions_separated : 65536+2048*100 ≤ dataBBase 100 := data_input_regions_disjoint 100
theorem data_b_100_base : dataBBase 100 = 270336 := by decide

theorem reset_final_accumulator_rejected : ¬Wgmma.Arithmetic (a 2) (b 2) (fun _ => 0)
    (fun p => (dataIterationCall a b 3 2 p.1).output p.2) := by
  intro h
  have hx := h (0,0)
  change (dataIterationCall a b 3 2 0).output 0 = Wgmma.results (a 2) (b 2) (fun _ => 0) (0,0) at hx
  rw [final_call_output] at hx
  norm_num [Wgmma.results,Wgmma.gatherC,Wgmma.scatterC,Wgmma.matrixStep,Wgmma.cCoord,a,b,
    Ptx.HopperDoubleBufferTests.nonuniformA,Ptx.HopperDoubleBufferTests.nonuniformB,Fin.sum_univ_succ] at hx

end
end Ptx.HopperDoubleBufferDataTests
