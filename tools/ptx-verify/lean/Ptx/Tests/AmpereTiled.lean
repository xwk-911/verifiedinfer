import Ptx.Generated.AmpereTiledMatmul
import Ptx.Ampere.Checked
import Ptx.Tests.MmaWarpGraph

/-! Real tiled PTX source slots and a two-iteration LOCAL source trace.
This single-lane trace is not a full launch or a memory-admitted witness. -/
namespace Ptx.AmpereTiledTests
open Ptx.ISA Ptx.Ampere
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def code := Generated.ampere_tiled_matmul.program
def params : Bindings := [("A",0),("B",2048),("C",4096),("M",16),("N",8),("K",32)]
def block : Dim3 := ⟨4,8,1⟩
def thread : ThreadId := ⟨.zero,.zero⟩
def oracle : Oracle := {
  scalar := fun _ => .integer 0
  bytes := fun _ => (PackedF16.mk 1 1).encode ++ (PackedF16.mk 1 1).encode
  word32 := fun _ => .packed ⟨1,1⟩
  matrix := fun q _ => if q = 9 then 16 else 32
}
def result : State × List Event :=
  ((Ampere.run {id := thread,params := params,block := block} oracle code 106 {}).toOption).getD ({},[])
def trace : ThreadTrace := ⟨thread,oracle,106,result.1,result.2⟩
def candidate : Candidate := ⟨[trace]⟩

theorem source_run_succeeded :
    (Ampere.run {id := thread,params := params,block := block} oracle code 106 {}).toOption.isSome = true := by rfl

theorem source_produced : Ampere.Produced code params block trace := by
  change Ampere.run {id := thread,params := params,block := block} oracle code 106 {} = .ok result
  have hh := source_run_succeeded
  cases hs : Ampere.run {id := thread,params := params,block := block} oracle code 106 {} with
  | error fault =>
    rw [hs] at hh
    change false = true at hh
    cases hh
  | ok value => simp only [result,hs,Except.toOption,Option.getD_some]
theorem source_done : trace.final.scalar.core.thread.status = .done := by rfl
theorem source_query_count : trace.final.scalar.core.queries = 20 := by rfl
theorem source_mma_count : trace.final.mmaCalls = 2 := by rfl
theorem source_copy_count : trace.final.copies.length = 6 := by rfl
theorem source_groups : trace.final.groups = 2 := by rfl
theorem source_barrier_generations : trace.final.scalar.core.generations = [(0,4)] := by rfl
theorem source_event_count : trace.events.length = 38 := by rfl

theorem actual_loop_backedge : code[77]? = some (.scalar (.integer (.jump 57))) := by rfl
theorem actual_zero_k_exit : code[58]? = some (.scalar (.integer (.branch "%p" true 78))) := by rfl
theorem actual_mma_slot : code[71]? = some (.mma ⟨"%acc0","%acc1","%acc2","%acc3"⟩
    ⟨"%ra0","%ra1","%ra2","%ra3"⟩ ⟨"%rb0","%rb1"⟩ ⟨"%acc0","%acc1","%acc2","%acc3"⟩) := by rfl

theorem source_first_publication_pc : sourcePC candidate code params block ⟨thread,6⟩ = some 64 := by rfl
theorem source_first_reuse_pc : sourcePC candidate code params block ⟨thread,16⟩ = some 72 := by rfl
theorem source_second_publication_pc : sourcePC candidate code params block ⟨thread,23⟩ = some 64 := by rfl
theorem source_second_reuse_pc : sourcePC candidate code params block ⟨thread,33⟩ = some 72 := by rfl
theorem dynamic_matching_required : uniqueBarrierSites code = false := by decide

def secondCall : MmaCall := match (trace.events[31]? : Option Event) with
  | some (.mmaReturn call) => call
  | _ => MmaLocalTests.fallback
theorem second_mma_ordinal : secondCall.ordinal = 1 := by rfl
theorem second_mma_captured_previous_c (slot : Fin 4) : secondCall.inputs.c slot = 16 := by
  fin_cases slot <;> rfl
theorem final_store : candidate.eventAt ⟨thread,34⟩ = some (.ordinary (.write ⟨.global,4096⟩ (Symbolic.encode .f32 32))) := by rfl

end
end Ptx.AmpereTiledTests
