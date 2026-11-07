import Ptx.Kernels.HopperDoubleBufferKernelReconstruction

/-! Source-only complete candidates with independent per-lane replies and
retry schedules. No cross-lane collective, resource, memory or tensor admission
is implied. This supplies nonvacuous tests of arbitrary-source inventory rules.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def replyTrace (tiles : Nat) (replies : Wgmma.Lane → Wgmma.Oracle) (schedules : Wgmma.Lane → Nat → Nat) (lane : Wgmma.Lane) : Unified.ThreadTrace := {
  id := (ctx tiles lane).id,oracle := replies lane,count := replyPositiveSteps tiles lane (schedules lane)
  final := replyPositiveState tiles lane (replies lane) (schedules lane)
  events := replyPositiveEvents tiles lane (replies lane) (schedules lane)
}
def replyCandidate (tiles : Nat) (replies : Wgmma.Lane → Wgmma.Oracle) (schedules : Wgmma.Lane → Nat → Nat) : Unified.Candidate :=
  ⟨List.ofFn (replyTrace tiles replies schedules)⟩

theorem reply_source_ids_unique (tiles replies schedules) :
    ((replyCandidate tiles replies schedules).traces.map Unified.ThreadTrace.id).Nodup := by
  simpa only [replyCandidate,List.map_ofFn,Function.comp_def,replyTrace,ctx] using
    (show (List.ofFn (fun lane : Wgmma.Lane => (HopperStage.ctx lane).id)).Nodup from by decide)

theorem reply_candidate_complete (tiles replies schedules) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.Complete (replyCandidate tiles replies schedules) := by
  intro trace hm
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hm
  apply outputState_complete
  exact (loopCheckpoint_ready (ctx tiles lane) (replies lane) 0 tiles (HopperStage.leader lane) (schedules lane)
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
    rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht tiles (by omega)).2.2.1

theorem reply_candidate_well_formed (tiles replies schedules initial) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hshape : ∀ lane, HopperStage.leader lane = true → ((replies lane).base.tmaBytes 1).length = ((replies lane).base.descriptor 0).bytes ∧
      ((replies lane).base.tmaBytes 3).length = ((replies lane).base.descriptor 2).bytes)
    (hreplies : ∀ lane i, i < tiles → LoopReplies (replies lane)
      (loopQuery 0 tiles (HopperStage.leader lane) (schedules lane) (if HopperStage.leader lane then 4 else 0) i)
      i tiles (schedules lane i) (HopperStage.leader lane)) :
    Unified.WellFormed code (completeLaunch tiles initial) (replyCandidate tiles replies schedules) := by
  refine ⟨by simp [completeLaunch,HopperStage.geometry,HopperStage.block,Geometry.Valid,Dim3.Positive,Dim3.one],reply_source_ids_unique tiles replies schedules,?_,?_⟩
  · intro trace hm
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp hm
    exact ⟨HopperStage.ctx_valid lane,positive_complete_any_reply tiles lane (replies lane) (schedules lane) ht hb
      (hshape lane) (hreplies lane)⟩
  · intro id hi
    obtain ⟨lane,he⟩ := HopperStage.ctx_covered hi
    exact ⟨replyTrace tiles replies schedules lane,List.mem_ofFn.mpr ⟨lane,rfl⟩,he⟩

end
end Ptx.Kernels.HopperDoubleBuffer
