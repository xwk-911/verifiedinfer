import Ptx.Kernels.HopperDoubleBufferHeader
import Ptx.Kernels.HopperDoubleBufferProbeMetadata

/-! Small actual-source projections exercise both selection paths, retries and
phase reuse. Assertions compare only decidable metadata, never real/function
state equality. The all-tile/all-context claim is header_execute, with explicit
loop-entry assumptions; these checks do not discharge launch admission. -/
namespace Ptx.HopperDoubleBufferControlTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def seed (tile : Nat) : Wgmma.State := {
  base := {scalar := {
    core := {thread := {pc := 45,regs := ("%tile",tile)::selectionBindings tile},queries := 7}
    floats := [("%d0",(.f32,17)),("%d1",(.f32,23)),("%d2",(.f32,41)),("%d3",(.f32,59))]
  }}
}
def retryOracle (failed : Nat) : Wgmma.Oracle :=
  {oracle 7 with base := {(oracle 7).base with wait := fun q => decide (7+failed ≤ q)}}
def controlResult (tile failed : Nat) :=
  (Wgmma.run (ctx 7 127) (retryOracle failed) code (headerSteps tile failed) (seed tile)).toOption
def registers (tile failed : Nat) : Option (List (Option Nat)) :=
  (controlResult tile failed).map fun r =>
    ["%waitbar","%ad","%bd","%parity","%phase0","%phase1","%ready","%tile"].map
      (fun name => lookup name r.1.base.scalar.core.thread.regs)
def pcQueries (tile failed : Nat) : Option (Nat × Nat) :=
  (controlResult tile failed).map fun r => (r.1.base.scalar.core.thread.pc,r.1.base.scalar.core.queries)
def waits (tile failed : Nat) : Option (List (Nat × Nat × Bool)) :=
  (controlResult tile failed).map fun r => r.2.filterMap waitMetadata

theorem even_header_registers : registers 0 0 = some
    [some 0,some 68720001025,some 68720001153,some 0,some 1,some 0,some 1,some 0] := by decide
theorem odd_header_registers : registers 1 0 = some
    [some 8,some 68720001169,some 68720001297,some 0,some 1,some 1,some 1,some 1] := by decide
theorem first_stage_reuse_registers : registers 2 3 = some
    [some 0,some 68720001025,some 68720001153,some 1,some 0,some 1,some 1,some 2] := by decide
theorem second_stage_reuse_registers : registers 3 1 = some
    [some 8,some 68720001169,some 68720001297,some 1,some 0,some 0,some 1,some 3] := by decide
theorem parity_wrap_registers : registers 4 3 = some
    [some 0,some 68720001025,some 68720001153,some 0,some 1,some 0,some 1,some 4] := by decide
theorem retries_consume_queries : pcQueries 2 3 = some (61,11) := by decide
theorem odd_retry_consumes_queries : pcQueries 3 1 = some (61,9) := by decide
theorem even_without_retry_consumes_one_query : pcQueries 0 0 = some (61,8) := by decide
theorem failed_waits_retained : waits 2 3 = some [(0,1,false),(0,1,false),(0,1,false),(0,1,true)] := by decide
theorem odd_failed_wait_retained : waits 3 1 = some [(8,1,false),(8,1,true)] := by decide

def accumulatorName (i : Fin 4) : String := if i.val = 0 then "%d0" else if i.val = 1 then "%d1" else if i.val = 2 then "%d2" else "%d3"
theorem arbitrary_accumulators_preserved (s : Wgmma.State) (tile retries : Nat)
    (hn : ∀ i : Fin 4, lookup (accumulatorName i) s.base.scalar.core.thread.regs = none) :
    ∀ i : Fin 4, declarationLookup (accumulatorName i) (headerState s tile retries).base.scalar.floats =
      declarationLookup (accumulatorName i) s.base.scalar.floats := by
  intro i
  apply headerState_float_frame s tile retries (accumulatorName i) _ (hn i)
  fin_cases i <;> decide

end
end Ptx.HopperDoubleBufferControlTests
