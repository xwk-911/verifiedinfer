import Ptx.Kernels.HopperDoubleBufferValueProtocol
import Ptx.Iris.ByteContentsPreparationExecution

/-! Native public preparation, actual source byte values and source-matched
device drain/acquire in one language from the initial no-loan protocol.
This does not allocate physical CUDA memory or interpret scalar protocol
buffer values as GPU bytes. Full-source adequacy retains whole-map ownership.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def preparationContext {tiles candidate} (family : ReplySourceFamily tiles candidate) : ByteContentsPreparation.Context :=
  ⟨valueProtocolContext family,Whole.commands tiles,0⟩
def publicPreparationActions (tiles : Nat) := ByteContentsPreparation.requests (Whole.requests tiles) ++ [.seal]
def publicValueActions (tiles : Nat) (actions : List ByteContentsHeap.Action) :=
  publicPreparationActions tiles ++ ByteContentsPreparation.execution (valuePipelineActions tiles actions)

theorem retry_data_native_preparation (a b tiles schedules frame values) (hv : values.length = 10) :
    IrisExecution.run (ByteContentsPreparation.transition (preparationContext (retryDataFamily a b tiles schedules))) (publicPreparationActions tiles)
      (retryValueInitialState a b tiles schedules frame (Ptx.Async.initial 1 values)) =
      .ok (retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles)) ∧
    ByteContentsPreparation.Enabled (preparationContext (retryDataFamily a b tiles schedules))
      (retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles)) := by
  let ctx := preparationContext (retryDataFamily a b tiles schedules)
  let state := retryValueInitialState a b tiles schedules frame (Ptx.Async.initial 1 values)
  have hp : ByteContentsPreparation.CanPrepare ctx state :=
    ⟨⟨fun _ h => h,ByteContentsHeap.initial_cells_available _ _ _⟩,rfl⟩
  have hr : Ptx.Async.Preparation.Ready state.coupled.protocol [] := Ptx.Async.Preparation.ready_initial values
  obtain ⟨next,hrun,hen,hcells,hcut,hpublic⟩ := ByteContentsPreparation.prepare_run ctx (Whole.requests tiles) state hp hr
    (by simpa only [state,retryValueInitialState,Ptx.Async.initial,List.length_map] using Whole.requests_valid values hv tiles) rfl
  change Ptx.Async.run (Ptx.Async.initial 1 values) (Whole.prepareActions tiles) = .ok next.coupled.protocol at hpublic
  have he : next.coupled.protocol = Whole.prepared values tiles := Except.ok.inj (hpublic.symm.trans (Whole.preparation_succeeds values hv tiles))
  have hn : next = retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles) := by
    apply congrArg₂ ByteContents.State.mk
    · exact congrArg₂ Bridge.State.mk he hcut
    · exact hcells
  rw [hn] at hrun hen
  exact ⟨hrun,hen⟩

theorem retry_data_public_value_output_of_run {a b tiles schedules frame values actions next}
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hr : IrisExecution.run (ByteContentsPreparation.transition (preparationContext (retryDataFamily a b tiles schedules))) actions
      (retryValueInitialState a b tiles schedules frame (Ptx.Async.initial 1 values)) = .ok next)
    (hcut : next.coupled.done = Present (retryDataCandidate a b tiles schedules))
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt next ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      some (.realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val) := by
  apply retry_data_value_output_of_unique_writes ht hb _ hcut lane slot index
  exact ByteContentsPreparation.unique_writes_run (preparationContext (retryDataFamily a b tiles schedules)) actions
    (ByteContentsHeap.unique_writes_initial (by intro node h; exact h)) hr

theorem retry_data_public_value_witness (a b tiles schedules frame values) (hv : values.length = 10)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∃ actions final,
      IrisExecution.run (ByteContentsPreparation.transition (preparationContext (retryDataFamily a b tiles schedules))) (publicValueActions tiles actions)
        (retryValueInitialState a b tiles schedules frame (Ptx.Async.initial 1 values)) = .ok final ∧
      final.coupled = ⟨Whole.returned values tiles,Present (retryDataCandidate a b tiles schedules)⟩ ∧
      ByteContentsHeap.Available final ∧ Ptx.Async.Drain.Returned final.coupled.protocol ∧ Ptx.Async.Preparation.Live final.coupled.protocol ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4), ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
        some (.realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val)) ∧
      (∀ bid, bid < 10 → (∃ next, Ptx.Async.reclaim final.coupled.protocol bid = .ok next) ∧
        ∀ value, ∃ next, Ptx.Async.hostWrite final.coupled.protocol bid value = .ok next) ∧
      adequate .NotStuck (ByteContentsPreparation.script (preparationContext (retryDataFamily a b tiles schedules)) (publicValueActions tiles actions))
        (retryValueInitialState a b tiles schedules frame (Ptx.Async.initial 1 values)) (fun result _ => result = .ok final) := by
  obtain ⟨hp,he⟩ := retry_data_native_preparation a b tiles schedules frame values hv
  obtain ⟨actions,final,hr,hcut,ha,hreturned,hlive,hm,hreuse,_,_⟩ := retry_data_value_pipeline_witness a b tiles schedules frame values hv ht hb
  have hexec := (ByteContentsPreparation.execution_run (preparationContext (retryDataFamily a b tiles schedules)) (valuePipelineActions tiles actions) he hr).1
  have hrun : IrisExecution.run (ByteContentsPreparation.transition (preparationContext (retryDataFamily a b tiles schedules))) (publicValueActions tiles actions)
      (retryValueInitialState a b tiles schedules frame (Ptx.Async.initial 1 values)) = .ok final := by
    rw [publicValueActions,IrisExecution.run_append,hp]
    exact hexec
  exact ⟨actions,final,hrun,hcut,ha,hreturned,hlive,hm,hreuse,ByteContentsPreparation.script_adequate _ _ _ _ hrun⟩

theorem public_prepared_active_blocks_host (a b tiles schedules frame values) (hv : values.length = 10)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) {actions state loc node mode target region}
    (hr : IrisExecution.run (ByteContentsPreparation.transition (preparationContext (retryDataFamily a b tiles schedules)))
      (publicPreparationActions tiles ++ ByteContentsPreparation.execution actions)
      (retryValueInitialState a b tiles schedules frame (Ptx.Async.initial 1 values)) = .ok state)
    (hheld : get? (ByteContents.erase state).bytes (ByteAuthority.key loc) = some (.held node mode))
    (hl : Whole.layout tiles target = some region) (hcontains : region.Contains loc) :
    ByteContentsPreparation.transition (preparationContext (retryDataFamily a b tiles schedules)) (.execute (.protocol (.host (.reclaim target)))) state =
        .error (.authority (.protocolFailure .outstandingLoan)) ∧
      ∀ value, ByteContentsPreparation.transition (preparationContext (retryDataFamily a b tiles schedules)) (.execute (.protocol (.host (.write target value)))) state =
        .error (.authority (.protocolFailure .outstandingLoan)) := by
  obtain ⟨hp,he⟩ := retry_data_native_preparation a b tiles schedules frame values hv
  rw [IrisExecution.run_append,hp] at hr
  have hr' : IrisExecution.run (ByteContentsPreparation.transition (preparationContext (retryDataFamily a b tiles schedules)))
      (ByteContentsPreparation.execution actions) (retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles)) = .ok state := hr
  have hs := ByteContentsPreparation.execution_projects _ actions hr'
  have hen := (ByteContentsPreparation.execution_run _ actions he hs).2
  have hg := retry_value_pipeline_active_blocks_host a b tiles schedules frame values hv ht hb hs hheld hl hcontains
  exact ⟨by rw [ByteContentsPreparation.execution_step hen]; exact hg.1,
    fun value => by rw [ByteContentsPreparation.execution_step hen]; exact hg.2 value⟩

end
end Ptx.Kernels.HopperDoubleBuffer
