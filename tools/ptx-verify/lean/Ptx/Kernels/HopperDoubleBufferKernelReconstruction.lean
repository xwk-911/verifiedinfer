import Ptx.Kernels.HopperDoubleBufferOutputReconstruction

/-! Exact full-thread source reconstruction for arbitrary replies and finite
completion at the canonical parameters/geometry. Captured matrix values remain
arbitrary; full-Pre candidate refinement, resource/memory/observer admission
and runtime correspondence are not inferred by source reconstruction. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def replyCheckpoint (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) : LoopCheckpoint :=
  loopCheckpoint (ctx tiles lane) reply 0 tiles (HopperStage.leader lane) retries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) tiles
def replyPositiveSteps (tiles : Nat) (lane : Wgmma.Lane) (retries : Nat → Nat) : Nat :=
  initialSteps (HopperStage.leader lane)+loopFuel 0 tiles (HopperStage.leader lane) retries tiles+outputSteps (HopperStage.leader lane)
def replyPositiveState (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) : Wgmma.State :=
  outputState (replyCheckpoint tiles lane reply retries).1 lane (HopperStage.leader lane)
def replyPositiveEvents (tiles : Nat) (lane : Wgmma.Lane) (reply : Wgmma.Oracle) (retries : Nat → Nat) : List Wgmma.Event :=
  initializationEvents (HopperStage.leader lane)++replyInitialCopies reply (HopperStage.leader lane)++
    (loopEvents (ctx tiles lane) reply 0 tiles (HopperStage.leader lane) retries
      (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224 tiles++
     outputEvents (ctx tiles lane) (replyCheckpoint tiles lane reply retries).1 lane (HopperStage.leader lane)
       (replyCheckpoint tiles lane reply retries).2)

theorem completed_positive_source_reconstruct {tiles lane reply count last events}
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hn : Wgmma.run (ctx tiles lane) reply code count {} = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    ∃ retries, (HopperStage.leader lane = true → (reply.base.tmaBytes 1).length = (reply.base.descriptor 0).bytes ∧
      (reply.base.tmaBytes 3).length = (reply.base.descriptor 2).bytes) ∧
      (∀ i < tiles, LoopReplies reply (loopQuery 0 tiles (HopperStage.leader lane) retries (if HopperStage.leader lane then 4 else 0) i)
        i tiles (retries i) (HopperStage.leader lane)) ∧
      count = replyPositiveSteps tiles lane retries ∧ last = replyPositiveState tiles lane reply retries ∧
      events = replyPositiveEvents tiles lane reply retries := by
  have hshape := completed_kernel_initial_shapes ht hb hn hd
  have hinit := positive_initial_any_reply tiles lane reply ht hb hshape
  have hic := Wgmma.completed_after_running_prefix hn hd hinit (by rfl)
  obtain ⟨loopAndOutput,hlooprun,htotal⟩ := Wgmma.run_suffix_of_prefix (Nat.le_of_lt hic) hn hinit
  obtain ⟨retries,hreplies,hfuel,hpc,hpending,tail,hout,hevents⟩ := completed_loop_reconstruct (by rfl) (by rfl) (by rfl) (Nat.le_refl 0)
    (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht hb hlooprun hd
  simp only [Nat.sub_zero] at hreplies hfuel hpc hpending hout hevents
  have hready := loopCheckpoint_ready (ctx tiles lane) reply 0 tiles (HopperStage.leader lane) retries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
    rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht tiles (by omega)
  obtain ⟨hcount,hstate,htail⟩ := completed_output_reconstruct hready.1 hpc hpending
    (loop_output_registers_any_reply tiles lane reply retries ht hb) hready.2.2.2.2.2 hout hd
  refine ⟨retries,hshape,?_,?_,hstate,?_⟩
  · simpa only [Nat.zero_add,initialLoopState] using hreplies
  · dsimp only [replyPositiveSteps]
    omega
  · rw [htotal,hevents,htail]
    simp only [replyPositiveEvents,List.append_assoc,replyCheckpoint]

theorem completed_source_cases {tiles lane reply count last events} (hb : tiles ≤ 2^28)
    (hn : Wgmma.run (ctx tiles lane) reply code count {} = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    (tiles = 0 ∧ count = completeSteps 0 lane ∧ last = completeState 0 lane ∧ events = completeEvents 0 lane) ∨
      (0 < tiles ∧ ∃ retries, count = replyPositiveSteps tiles lane retries ∧ last = replyPositiveState tiles lane reply retries ∧
        events = replyPositiveEvents tiles lane reply retries) := by
  by_cases hz : tiles = 0
  · subst tiles
    exact Or.inl ⟨rfl,completed_zero_source_reconstruct hn hd⟩
  · have ht := Nat.pos_of_ne_zero hz
    obtain ⟨retries,_,_,hc,hs,he⟩ := completed_positive_source_reconstruct ht hb hn hd
    exact Or.inr ⟨ht,retries,hc,hs,he⟩

theorem positive_complete_any_reply (tiles lane) (reply : Wgmma.Oracle) (retries : Nat → Nat)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hshape : HopperStage.leader lane = true → (reply.base.tmaBytes 1).length = (reply.base.descriptor 0).bytes ∧
      (reply.base.tmaBytes 3).length = (reply.base.descriptor 2).bytes)
    (hreplies : ∀ i < tiles, LoopReplies reply (loopQuery 0 tiles (HopperStage.leader lane) retries (if HopperStage.leader lane then 4 else 0) i)
      i tiles (retries i) (HopperStage.leader lane)) :
    Wgmma.run (ctx tiles lane) reply code (replyPositiveSteps tiles lane retries) {} =
      .ok (replyPositiveState tiles lane reply retries,replyPositiveEvents tiles lane reply retries) := by
  have hinit := positive_initial_any_reply tiles lane reply ht hb hshape
  have hloop := loop_execute (ctx tiles lane) reply 0 tiles (HopperStage.leader lane) retries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
    rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht hb tiles (by omega)
    (by simpa only [Nat.zero_add,initialLoopState] using hreplies)
  have hready := loopCheckpoint_ready (ctx tiles lane) reply 0 tiles (HopperStage.leader lane) retries
    (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
    rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht tiles (by omega)
  obtain ⟨hx,hy,hz,ho,hl,hb0,hb1⟩ := loop_output_registers_any_reply tiles lane reply retries ht hb
  have hpc : (replyCheckpoint tiles lane reply retries).1.base.scalar.core.thread.pc = 85 := by
    dsimp only [replyCheckpoint]
    simpa only [Nat.zero_add,lt_self_iff_false,ite_false] using hready.2.1
  have hout := output_execute (ctx tiles lane) reply (replyCheckpoint tiles lane reply retries).1 lane (HopperStage.leader lane)
    (replyCheckpoint tiles lane reply retries).2 hready.1 hpc hready.2.2.1 hx hy hz ho hl hb0 hb1 hready.2.2.2.2.2
  dsimp only [replyCheckpoint] at hout
  rw [replyPositiveSteps,Wgmma.run_add,Wgmma.run_add,hinit]
  simp only [Except.bind,hloop,hout,replyCheckpoint,replyPositiveState,replyPositiveEvents,List.append_assoc]

theorem candidate_trace_run {tiles initial candidate trace}
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (ht : trace ∈ candidate.traces) :
    ∃ lane : Wgmma.Lane, trace.id = (ctx tiles lane).id ∧
      Wgmma.run (ctx tiles lane) trace.oracle code trace.count {} = .ok (trace.final,trace.events) := by
  have hvalid := (hw.2.2.1 trace ht).1
  obtain ⟨lane,hid⟩ := HopperStage.ctx_covered hvalid
  have hsource := (hw.2.2.1 trace ht).2
  refine ⟨lane,hid.symm,?_⟩
  change Wgmma.run {id := trace.id,params := params tiles,block := HopperStage.block} trace.oracle code trace.count {} = .ok (trace.final,trace.events) at hsource
  rw [← hid] at hsource
  exact hsource

theorem completed_candidate_trace_reconstruct {tiles initial candidate trace} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (ht : trace ∈ candidate.traces) :
    ∃ lane : Wgmma.Lane, trace.id = (ctx tiles lane).id ∧
      ((tiles = 0 ∧ trace.count = completeSteps 0 lane ∧ trace.final = completeState 0 lane ∧ trace.events = completeEvents 0 lane) ∨
       (0 < tiles ∧ ∃ retries, trace.count = replyPositiveSteps tiles lane retries ∧
         trace.final = replyPositiveState tiles lane trace.oracle retries ∧ trace.events = replyPositiveEvents tiles lane trace.oracle retries)) := by
  obtain ⟨lane,hid,hrun⟩ := candidate_trace_run hw ht
  exact ⟨lane,hid,completed_source_cases hb hrun (hc trace ht).1⟩

end
end Ptx.Kernels.HopperDoubleBuffer
