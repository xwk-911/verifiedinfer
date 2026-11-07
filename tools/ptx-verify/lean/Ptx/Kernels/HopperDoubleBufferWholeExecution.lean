import Ptx.Kernels.HopperDoubleBufferWholeCoverage

/-! One public prepare/drain/acquire path for all ten modeled regions. Source
completion guards retain individual TMA/native waits and whole-kernel roots.
No physical scheduling fairness, CUDA allocation or byte-value simulation follows.
-/
namespace Ptx.Kernels.HopperDoubleBuffer.Whole
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

theorem return_exists (values : List Nat) (hv : values.length = 10) (tiles : Nat) :
    ∃ state, Ptx.Async.run (prepared values tiles) (returnActions tiles) = .ok state ∧
      Ptx.Async.Drain.Returned state ∧ Ptx.Async.Preparation.Live state ∧ state.buffers.length = 10 ∧
      state.streams = [⟨6*tiles+2,6*tiles+2,[],[]⟩] := by
  have hp := prepared_properties values hv tiles
  obtain ⟨state,hr,hn,hl,hb,hs⟩ := Ptx.Async.Drain.drain_and_acquire hp.1 (prepared_invariant values hv tiles)
    (Ptx.Async.Drain.requests_plain (requests tiles)) (by simpa only [commands_length] using hp.2.2)
  exact ⟨state,by simpa only [returnActions,commands_length] using hr,hn,hl,hb.trans hp.2.1,by simpa only [commands_length] using hs⟩

theorem return_succeeds (values : List Nat) (hv : values.length = 10) (tiles : Nat) :
    Ptx.Async.run (prepared values tiles) (returnActions tiles) = .ok (returned values tiles) := by
  obtain ⟨state,hs,_⟩ := return_exists values hv tiles
  simp only [returned,hs,Except.toOption,Option.getD_some]

theorem returned_properties (values : List Nat) (hv : values.length = 10) (tiles : Nat) :
    Ptx.Async.Drain.Returned (returned values tiles) ∧ Ptx.Async.Preparation.Live (returned values tiles) ∧
      (returned values tiles).buffers.length = 10 ∧ (returned values tiles).streams = [⟨6*tiles+2,6*tiles+2,[],[]⟩] := by
  obtain ⟨state,hs,hr,hl,hb,he⟩ := return_exists values hv tiles
  have heq := Except.ok.inj (hs.symm.trans (return_succeeds values hv tiles))
  subst state
  exact ⟨hr,hl,hb,he⟩

theorem complete_public_client (values : List Nat) (hv : values.length = 10) (tiles : Nat) :
    Ptx.Async.run (Ptx.Async.initial 1 values) (prepareActions tiles ++ returnActions tiles) = .ok (returned values tiles) := by
  simp only [Ptx.Async.Client.run_append,preparation_succeeds values hv tiles,Except.bind,return_succeeds values hv tiles]

theorem returned_can_write (values : List Nat) (hv : values.length = 10) (tiles bid value : Nat) (hb : bid < 10) :
    ∃ state, Ptx.Async.hostWrite (returned values tiles) bid value = .ok state := by
  have hp := returned_properties values hv tiles
  have hlt : bid < (returned values tiles).buffers.length := by rw [hp.2.2.1]; exact hb
  have hg : (returned values tiles).buffers[bid]? = some (returned values tiles).buffers[bid] := List.getElem?_eq_getElem hlt
  have hget := Ptx.Async.getBuffer_iff.mpr ⟨hg,hp.2.1 _ _ hg⟩
  refine ⟨{returned values tiles with buffers := (returned values tiles).buffers.set bid {(returned values tiles).buffers[bid] with value := value}},?_⟩
  simp [Ptx.Async.hostWrite,hget,hp.1 _ _ hg,bind,Except.bind,pure,Except.pure]

theorem returned_can_reclaim (values : List Nat) (hv : values.length = 10) (tiles bid : Nat) (hb : bid < 10) :
    ∃ state, Ptx.Async.reclaim (returned values tiles) bid = .ok state := by
  have hp := returned_properties values hv tiles
  have hlt : bid < (returned values tiles).buffers.length := by rw [hp.2.2.1]; exact hb
  have hg : (returned values tiles).buffers[bid]? = some (returned values tiles).buffers[bid] := List.getElem?_eq_getElem hlt
  have hget := Ptx.Async.getBuffer_iff.mpr ⟨hg,hp.2.1 _ _ hg⟩
  refine ⟨{returned values tiles with buffers := (returned values tiles).buffers.set bid {(returned values tiles).buffers[bid] with alive := false}},?_⟩
  simp [Ptx.Async.reclaim,hget,hp.1 _ _ hg,bind,Except.bind,pure,Except.pure]

theorem plan_full_completed {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) (retryHistories family)) :
    Bridge.AllCompleted Tma.localShared candidate (retryHistories family) dataCluster (plan family) (Present candidate) := by
  intro ticket work hm
  unfold plan at hm
  split at hm
  · exact async_plan_full_completed family ht hb htma ticket work hm
  · split at hm
    · cases hm; exact .kernel htma.complete (fun _ h => h)
    · cases hm

theorem complete_coupled_run {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) (retryHistories family))
    (values : List Nat) (hv : values.length = 10) :
    Bridge.Steps HopperStage.block Tma.localShared candidate (retryHistories family) dataCluster (plan family)
      ⟨prepared values tiles,fun _ => False⟩ ⟨returned values tiles,Present candidate⟩ := by
  apply Bridge.steps_trans (Bridge.prefix_execution (prepared values tiles)
    (retry_family_full_prefix family ht hb htma.source htma.histories_valid))
  apply Bridge.completed_script_execution (plan_full_completed family ht hb htma) (returnCommands tiles)
  simpa [returnCommands,returnActions,Bridge.Command.action,Bridge.HostAction.action] using return_succeeds values hv tiles

end
end Ptx.Kernels.HopperDoubleBuffer.Whole
