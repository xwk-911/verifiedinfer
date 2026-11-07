import Ptx.Kernels.HopperStageNativeCompletion

/-! Actual generated-source prefixes stop after commit, before the native
wait. Every physical lane has issued MMA, but the pending operation has no
observed native completion. This is a source prefix, not a complete launch.
-/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def committed31 (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) : Wgmma.State := {
  base := {scalar := {
    core := {
      thread := {pc := 31,regs := ("%ready",1)::prefixRegs lane (if isLeader then 1 else 0)}
      queries := queryAt29 isLeader+1
      generations := [(0,1)]
    }
    floats := zeroFloats
  }}
  ledger := {fenced := true,groups := 1,calls := [stageCall a b lane isLeader],syncs := 3}
}
def issueCommitEvents (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) : List Wgmma.Event := [
  .mma (mmaMark lane) (stageCall a b lane isLeader),.commit ⟨30,2,Ampere.linearThread (ctx lane)/128⟩ 0]
theorem native_two_steps (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) (isLeader : Bool) :
    Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program 2 (at29 lane isLeader) =
      .ok (committed31 a b lane isLeader,issueCommitEvents a b lane isLeader) := by rfl
def prefixTrace (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) : Unified.ThreadTrace := {
  id := (ctx lane).id
  oracle := oracle a b lane
  count := 18+middleCount (leader lane)+2
  final := committed31 a b lane (leader lane)
  events := middleEvents a b lane (leader lane)++issueCommitEvents a b lane (leader lane)
}
def prefixCandidate (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) : Unified.Candidate := ⟨List.ofFn (prefixTrace a b)⟩
theorem prefix_produced (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Unified.Produced Generated.hopper_gemm_stage.program params block (prefixTrace a b lane) := by
  change Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program (18+middleCount (leader lane)+2) {} = _
  rw [Wgmma.run_add,source_prefix_29]
  simp only [Except.bind,native_two_steps]
  rfl
theorem prefix_pending (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    (Wgmma.pending (prefixTrace a b lane).final.ledger).length = 1 := by rfl
theorem prefix_ids_unique (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    ((prefixCandidate a b).traces.map Unified.ThreadTrace.id).Nodup := by
  simpa only [prefixCandidate,List.map_ofFn,Function.comp_def,prefixTrace] using
    (show (List.ofFn (fun lane : Wgmma.Lane => (ctx lane).id)).Nodup from by decide)
theorem prefix_actual_mma (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    (prefixCandidate a b).eventAt (mmaId lane) = some (.mma (mmaMark lane) (calls a b lane)) := by
  change (prefixCandidate a b).eventAt ⟨(prefixTrace a b lane).id,middleLength (leader lane)⟩ = _
  rw [Unified.eventAt_of_member (prefix_ids_unique a b) (List.mem_ofFn.mpr ⟨lane,rfl⟩)]
  change (middleEvents a b lane (leader lane)++issueCommitEvents a b lane (leader lane))[middleLength (leader lane)]? = _
  rw [← middle_length a b lane (leader lane),List.getElem?_append_right (by omega)]
  simp only [Nat.sub_self,issueCommitEvents,List.getElem?_cons_zero,calls]
def prefix_collective (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) : Unified.Collective (prefixCandidate a b) (mmaId 0) := {
  calls := calls a b
  marks := mmaMark
  sources := mmaId
  representative := rfl
  matched := prefix_actual_mma a b
  sameCTA := fun _ => rfl
  sameMark := mark_same
  cohort := calls_cohort a b
}
theorem prefix_has_no_native_wait {a b id mark groups keep before after query} :
    (prefixCandidate a b).eventAt id ≠ some (.wait mark groups keep before after query) := by
  intro he
  obtain ⟨actual,ht,_,hget⟩ := Unified.eventAt_trace he
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  have hm := List.mem_of_getElem? hget
  change .wait mark groups keep before after query ∈ middleEvents a b lane (leader lane)++issueCommitEvents a b lane (leader lane) at hm
  cases hh : leader lane <;> simp [hh,middleEvents,issueCommitEvents] at hm
theorem prefix_no_completion (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (issue wait : Ptx.Event.EventId) :
    ¬Unified.WgmmaCompletedAt (prefixCandidate a b) issue wait :=
  Unified.no_wait_no_native_completion (fun _ _ _ _ _ _ => prefix_has_no_native_wait)
theorem prefix_cannot_justify_reuse (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ)
    (resolve : Tma.SharedResolver) (loc : Location) (issue : Ptx.Event.EventId) (operand : Wgmma.OperandByte) (target : Unified.Node) :
    ¬Unified.NativeReuse resolve (prefixCandidate a b) loc (.wgmmaRead issue operand) target :=
  Unified.no_completion_no_native_reuse (prefix_no_completion a b issue)

end
end Ptx.Kernels.HopperStage
