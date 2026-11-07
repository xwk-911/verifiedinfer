import Ptx.Async.Drain
import Ptx.Kernels.HopperDoubleBufferPreparedLoans
import Ptx.Kernels.HopperDoubleBufferAsyncCompletion

/-! Parameterized public drain/return and its coupled actual-prefix execution.
This completes the prepared async lifetime client, not ordinary/resource source
ownership, byte-value simulation or physical CUDA runtime refinement. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def loanReturnActions (tiles : Nat) : List Ptx.Async.Action :=
  List.replicate (6*tiles) (.device 0) ++ [.acquire (tiles+1)]
def loanReturnCommands (tiles : Nat) : List Bridge.Command :=
  List.replicate (6*tiles) (.device 0) ++ [.host (.acquire (tiles+1))]
def publicReturned (values : List Nat) (tiles : Nat) : Ptx.Async.State :=
  (Ptx.Async.run (publicPrepared values tiles) (loanReturnActions tiles)).toOption.getD (publicPrepared values tiles)

theorem async_commands_plain (tiles : Nat) : Ptx.Async.Drain.Plain (asyncCommands tiles) := by
  intro command hm ticket
  obtain ⟨tile,_,hmem⟩ := List.mem_flatMap.mp hm
  exact Ptx.Async.Drain.requests_plain (tileRequests tile) command hmem ticket

theorem public_return_exists (values : List Nat) (hv : values.length = 8) (tiles : Nat) :
    ∃ state, Ptx.Async.run (publicPrepared values tiles) (loanReturnActions tiles) = .ok state ∧
      Ptx.Async.Drain.Returned state ∧ Ptx.Async.Preparation.Live state ∧ state.buffers.length = 8 ∧
      state.streams = [⟨6*tiles,6*tiles,[],[]⟩] := by
  have hp := public_prepared_properties values hv tiles
  obtain ⟨state,hr,hn,hl,hb,hs⟩ := Ptx.Async.Drain.drain_and_acquire hp.1 (public_prepared_invariant values hv tiles)
    (async_commands_plain tiles) (by simpa only [async_commands_length] using public_final_event values hv tiles)
  exact ⟨state,by simpa only [loanReturnActions,async_commands_length] using hr,hn,hl,hb.trans hp.2.1,
    by simpa only [async_commands_length] using hs⟩

theorem public_return_succeeds (values : List Nat) (hv : values.length = 8) (tiles : Nat) :
    Ptx.Async.run (publicPrepared values tiles) (loanReturnActions tiles) = .ok (publicReturned values tiles) := by
  obtain ⟨state,hs,_⟩ := public_return_exists values hv tiles
  simp only [publicReturned,hs,Except.toOption,Option.getD_some]

theorem public_returned_properties (values : List Nat) (hv : values.length = 8) (tiles : Nat) :
    Ptx.Async.Drain.Returned (publicReturned values tiles) ∧ Ptx.Async.Preparation.Live (publicReturned values tiles) ∧
      (publicReturned values tiles).buffers.length = 8 ∧ (publicReturned values tiles).streams = [⟨6*tiles,6*tiles,[],[]⟩] := by
  obtain ⟨state,hs,hr,hl,hb,he⟩ := public_return_exists values hv tiles
  have heq := Except.ok.inj (hs.symm.trans (public_return_succeeds values hv tiles))
  subst state
  exact ⟨hr,hl,hb,he⟩

theorem complete_lifetime_client_succeeds (values : List Nat) (hv : values.length = 8) (tiles : Nat) :
    Ptx.Async.run (Ptx.Async.initial 1 values) (preparationActions tiles ++ loanReturnActions tiles) = .ok (publicReturned values tiles) := by
  simp only [Ptx.Async.Client.run_append,public_preparation_succeeds values hv tiles,Except.bind,public_return_succeeds values hv tiles]

theorem returned_can_write (values : List Nat) (hv : values.length = 8) (tiles bid value : Nat) (hb : bid < 8) :
    ∃ state, Ptx.Async.hostWrite (publicReturned values tiles) bid value = .ok state := by
  have hp := public_returned_properties values hv tiles
  have hlt : bid < (publicReturned values tiles).buffers.length := by rw [hp.2.2.1]; exact hb
  have hg : (publicReturned values tiles).buffers[bid]? = some (publicReturned values tiles).buffers[bid] := List.getElem?_eq_getElem hlt
  have hget := Ptx.Async.getBuffer_iff.mpr ⟨hg,hp.2.1 _ _ hg⟩
  refine ⟨{publicReturned values tiles with buffers := (publicReturned values tiles).buffers.set bid {(publicReturned values tiles).buffers[bid] with value := value}},?_⟩
  simp [Ptx.Async.hostWrite,hget,hp.1 _ _ hg,bind,Except.bind,pure,Except.pure]

theorem returned_can_reclaim (values : List Nat) (hv : values.length = 8) (tiles bid : Nat) (hb : bid < 8) :
    ∃ state, Ptx.Async.reclaim (publicReturned values tiles) bid = .ok state := by
  have hp := public_returned_properties values hv tiles
  have hlt : bid < (publicReturned values tiles).buffers.length := by rw [hp.2.2.1]; exact hb
  have hg : (publicReturned values tiles).buffers[bid]? = some (publicReturned values tiles).buffers[bid] := List.getElem?_eq_getElem hlt
  have hget := Ptx.Async.getBuffer_iff.mpr ⟨hg,hp.2.1 _ _ hg⟩
  refine ⟨{publicReturned values tiles with buffers := (publicReturned values tiles).buffers.set bid {(publicReturned values tiles).buffers[bid] with alive := false}},?_⟩
  simp [Ptx.Async.reclaim,hget,hp.1 _ _ hg,bind,Except.bind,pure,Except.pure]

theorem public_complete_coupled_run {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) (retryHistories family))
    (values : List Nat) (hv : values.length = 8) :
    Bridge.Steps HopperStage.block Tma.localShared candidate (retryHistories family) dataCluster (asyncPlan family)
      ⟨publicPrepared values tiles,fun _ => False⟩ ⟨publicReturned values tiles,Present candidate⟩ := by
  have hp := retry_family_full_prefix family ht hb htma.source htma.histories_valid
  apply Bridge.steps_trans (Bridge.prefix_execution (publicPrepared values tiles) hp)
  apply Bridge.completed_script_execution (async_plan_full_completed family ht hb htma) (loanReturnCommands tiles)
  simpa [loanReturnCommands,loanReturnActions,Bridge.Command.action,Bridge.HostAction.action] using public_return_succeeds values hv tiles

end
end Ptx.Kernels.HopperDoubleBuffer
