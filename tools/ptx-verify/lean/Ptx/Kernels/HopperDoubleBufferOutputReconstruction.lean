import Ptx.Kernels.HopperDoubleBufferInitialReconstruction
import Ptx.Kernels.HopperDoubleBufferKernelSource
import Ptx.Kernels.HopperDoubleBufferLoopReconstruction

/-! Arbitrary-reply output reconstruction and the complete zero-tile source
path. These exact source states/events are not a memory/observer correctness
claim; positive matrix values still need the independent tensor rules. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem loop_output_registers_any_reply (tiles lane) (reply : Wgmma.Oracle) (retries : Nat → Nat)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    OutputRegisters (loopCheckpoint (ctx tiles lane) reply 0 tiles (HopperStage.leader lane) retries
      (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) tiles).1 lane (HopperStage.leader lane) := by
  have hframe (name : String)
      (hn : name ∉ ["%phase0","%phase1","%even","%waitbar","%ad","%bd","%parity","%ready",
        "%next","%more","%nextbar","%copya","%copyb","%ay","%slot","%tile","%d0","%d1","%d2","%d3"]) :=
    loopCheckpoint_control_frame (ctx tiles lane) reply 0 tiles (HopperStage.leader lane) retries
      (initialLoopState tiles lane (HopperStage.leader lane)) (fun _ => 0) 4096 4224
      rfl rfl rfl (Nat.le_refl 0) (initial_loop_registers tiles lane _ hb) (initial_loop_accumulators tiles lane _) ht tiles (by omega) name hn
  unfold OutputRegisters
  rw [hframe "%x" (by decide),hframe "%y" (by decide),hframe "%z" (by decide),hframe "%out" (by decide),
    hframe "%leader" (by decide),hframe "%bar0" (by decide),hframe "%bar1" (by decide)]
  cases he : HopperStage.leader lane <;> simp [initialLoopState,initialLoopRegs,entryRegs,lookup]

theorem completed_output_reconstruct {context reply s count last events lane leader values}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 85)
    (hp : Wgmma.pending s.ledger = []) (hregs : OutputRegisters s lane leader) (hacc : Accumulators s values)
    (hn : Wgmma.run context reply code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    count = outputSteps leader ∧ last = outputState s lane leader ∧ events = outputEvents context s lane leader values := by
  obtain ⟨hx,hy,hz,ho,hl,hb0,hb1⟩ := hregs
  have hout := output_execute context reply s lane leader values hr hpc hp hx hy hz ho hl hb0 hb1 hacc
  exact Wgmma.complete_run_unique hn hd hout (outputState_complete s lane leader hp).1

theorem zero_guard_any_reply (lane : Wgmma.Lane) (reply : Wgmma.Oracle) :
    Wgmma.run (ctx 0 lane) reply code (zeroTileSteps lane) {} =
      .ok (guardedInitialState 0 lane (HopperStage.leader lane) true,initializationEvents (HopperStage.leader lane)) := by
  rw [zeroTileSteps,Wgmma.run_add,Wgmma.run_add,entry_any_reply]
  simp only [Except.bind,initialize_any_reply,guard_any_reply 0 lane _ _ (by decide),decide_true,List.nil_append,List.append_nil]

theorem zero_complete_any_reply (lane : Wgmma.Lane) (reply : Wgmma.Oracle) :
    Wgmma.run (ctx 0 lane) reply code (completeSteps 0 lane) {} = .ok (completeState 0 lane,completeEvents 0 lane) := by
  obtain ⟨hx,hy,hz,ho,hl,hb0,hb1⟩ := zero_output_registers lane
  have hout := output_execute (ctx 0 lane) reply (guardedInitialState 0 lane (HopperStage.leader lane) true) lane
    (HopperStage.leader lane) (fun _ => 0) rfl rfl rfl hx hy hz ho hl hb0 hb1 (zero_output_accumulators lane)
  rw [completeSteps,preOutputSteps,ite_eq_left rfl,Wgmma.run_add,zero_guard_any_reply]
  simp only [Except.bind,hout,completeState,completeEvents,preOutputState,preOutputEvents,ite_true]

theorem completed_zero_source_reconstruct {lane reply count last events}
    (hn : Wgmma.run (ctx 0 lane) reply code count {} = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    count = completeSteps 0 lane ∧ last = completeState 0 lane ∧ events = completeEvents 0 lane :=
  Wgmma.complete_run_unique hn hd (zero_complete_any_reply lane reply) (complete_source_status 0 lane (by decide)).1

end
end Ptx.Kernels.HopperDoubleBuffer
