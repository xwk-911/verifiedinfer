import Ptx.Kernels.HopperStageFinish

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def result (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) : Wgmma.State × List Wgmma.Event :=
  ((tailResult a b lane (leader lane)).1,middleEvents a b lane (leader lane)++(tailResult a b lane (leader lane)).2)
def trace (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) : Unified.ThreadTrace := {
  id := (ctx lane).id
  oracle := oracle a b lane
  count := count lane
  final := (result a b lane).1
  events := (result a b lane).2
}
def candidate (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) : Unified.Candidate := ⟨List.ofFn (trace a b)⟩
def launch (initial : Location → Symbolic.Byte) : Scalar.Launch := ⟨geometry,params,initial⟩

theorem actual_run (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (count lane) {} = .ok (result a b lane) := by
  rw [total_count,Wgmma.run_add,source_prefix_29]
  simp only [Except.bind,tail_run]
  rfl
theorem all_runs_succeed (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    ∀ lane : Wgmma.Lane,
      (Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (count lane) {}).toOption.isSome = true := by
  intro lane
  rw [actual_run]
  rfl
theorem source_produced (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Unified.Produced Generated.hopper_gemm_stage.program params block (trace a b lane) := by
  change Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (count lane) {} =
    .ok ((result a b lane).1,(result a b lane).2)
  simpa only [Prod.mk.eta] using actual_run a b lane
theorem complete_metadata (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    ∀ lane : Wgmma.Lane, (((result a b lane).1.base.scalar.core.thread.status == .done) &&
      ((Wgmma.pending (result a b lane).1.ledger).length == 0)) = true := by
  intro lane
  exact tail_complete_metadata a b lane (leader lane)
theorem trace_complete (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Wgmma.Complete (trace a b lane).final := Wgmma.complete_of_metadata (result a b lane).1 (complete_metadata a b lane)
theorem source_complete (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) : Unified.Complete (candidate a b) := by
  intro trace ht
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  exact trace_complete a b lane
theorem trace_ids_unique (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    ((candidate a b).traces.map Unified.ThreadTrace.id).Nodup := by
  simpa only [candidate,List.map_ofFn,Function.comp_def,trace] using
    (show (List.ofFn (fun lane : Wgmma.Lane => (ctx lane).id)).Nodup from by decide)
theorem ctx_valid (lane : Wgmma.Lane) : (ctx lane).id.Valid geometry := by
  have := lane.isLt
  dsimp [ctx,ThreadId.Valid,geometry,block,tid,Dim3.Within,Dim3.zero,Dim3.one]
  omega
theorem ctx_covered {id : ThreadId} (hi : id.Valid geometry) : ∃ lane : Wgmma.Lane, (ctx lane).id = id := by
  rcases id with ⟨⟨cx,cy,cz⟩,⟨x,y,z⟩⟩
  dsimp [ThreadId.Valid,Dim3.Within,geometry,block,Dim3.one] at hi
  have hcx : cx = 0 := by omega
  have hcy : cy = 0 := by omega
  have hcz : cz = 0 := by omega
  subst cx; subst cy; subst cz
  refine ⟨⟨x+4*(y+8*z),by omega⟩,?_⟩
  dsimp [ctx,tid]
  congr 1
  congr 1 <;> omega
theorem source_well_formed (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (initial : Location → Symbolic.Byte) :
    Unified.WellFormed Generated.hopper_gemm_stage.program (launch initial) (candidate a b) := by
  refine ⟨by simp [launch,geometry,block,Geometry.Valid,Dim3.Positive,Dim3.one],trace_ids_unique a b,?_,?_⟩
  · intro trace ht
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨ctx_valid lane,source_produced a b lane⟩
  · intro id hi
    obtain ⟨lane,he⟩ := ctx_covered hi
    exact ⟨trace a b lane,List.mem_ofFn.mpr ⟨lane,rfl⟩,he⟩
theorem component_view_complete (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) : Hopper.Complete (candidate a b).view :=
  Unified.view_complete (source_complete a b)

end
end Ptx.Kernels.HopperStage
