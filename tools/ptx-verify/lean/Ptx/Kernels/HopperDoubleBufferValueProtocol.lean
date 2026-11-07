import Ptx.Kernels.HopperDoubleBufferValueOutput
import Ptx.Kernels.HopperDoubleBufferWholeExecution
import Ptx.Iris.ByteContentsProtocol

/-! A complete actual source/value/device/acquire execution from the publicly
prepared protocol and initial byte pool. The final real matrix and returned
modeled loans coexist in the same state. Public preparation is still a separate
checked interpreter run; physical host writes/reclamation are not byte effects
of this prepared-plan metadata language. Full-source native adequacy retains
the existing whole-map heap baseline.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris.ProgramLogic
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def valueProtocolContext {tiles candidate} (family : ReplySourceFamily tiles candidate) : ByteContentsProtocolHeap.Context :=
  ⟨byteContentsContext family,dataCluster,Whole.plan family⟩
def valuePipelineActions (tiles : Nat) (actions : List ByteContentsHeap.Action) :=
  ByteContentsProtocolHeap.sourceActions actions ++ ByteContentsProtocolHeap.protocolActions (Whole.returnCommands tiles)

theorem retry_data_value_protocol_output_of_run {a b tiles schedules frame protocol actions next}
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hr : IrisExecution.run (ByteContentsProtocolHeap.transition (valueProtocolContext (retryDataFamily a b tiles schedules))) actions
      (retryValueInitialState a b tiles schedules frame protocol) = .ok next)
    (hcut : next.coupled.done = Present (retryDataCandidate a b tiles schedules))
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt next ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      some (.realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val) := by
  apply retry_data_value_output_of_unique_writes ht hb _ hcut lane slot index
  exact ByteContentsProtocolHeap.unique_writes_run (valueProtocolContext (retryDataFamily a b tiles schedules)) actions
    (ByteContentsHeap.unique_writes_initial (by intro node h; exact h)) hr

theorem retry_data_value_pipeline_witness (a b tiles schedules frame values) (hv : values.length = 10)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∃ actions final,
      IrisExecution.run (ByteContentsProtocolHeap.transition (valueProtocolContext (retryDataFamily a b tiles schedules)))
        (valuePipelineActions tiles actions) (retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles)) = .ok final ∧
      final.coupled = ⟨Whole.returned values tiles,Present (retryDataCandidate a b tiles schedules)⟩ ∧
      ByteContentsHeap.Available final ∧
      Ptx.Async.Drain.Returned final.coupled.protocol ∧ Ptx.Async.Preparation.Live final.coupled.protocol ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4), ByteContents.valueAt final ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
        some (.realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val)) ∧
      (∀ bid, bid < 10 → (∃ next, Ptx.Async.reclaim final.coupled.protocol bid = .ok next) ∧
        ∀ value, ∃ next, Ptx.Async.hostWrite final.coupled.protocol bid value = .ok next) ∧
      adequate .NotStuck (ByteContentsProtocolHeap.script (valueProtocolContext (retryDataFamily a b tiles schedules)) (valuePipelineActions tiles actions))
        (retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles)) (fun result _ => result = .ok final) ∧
      ByteAuthority.Steps HopperStage.block (retryDataCandidate a b tiles schedules) (retryHistories (retryDataFamily a b tiles schedules))
        dataCluster (Whole.plan (retryDataFamily a b tiles schedules))
        (ByteContents.erase (retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles))) (ByteContents.erase final) := by
  let family := retryDataFamily a b tiles schedules
  obtain ⟨actions,mid,hs,hcut,hprotocol,ha,_⟩ := retry_data_value_source_run a b tiles schedules frame (Whole.prepared values tiles) ht hb
  have hc : Bridge.AllCompleted Tma.localShared (retryDataCandidate a b tiles schedules) (retryHistories family) dataCluster (Whole.plan family) mid.coupled.done := by
    rw [hcut]
    exact Whole.plan_full_completed family ht hb (retry_data_complete_components a b tiles schedules frame ht hb).1
  have hr : Ptx.Async.run mid.coupled.protocol ((Whole.returnCommands tiles).map Bridge.Command.action) = .ok (Whole.returned values tiles) := by
    rw [hprotocol]
    simpa [Whole.returnCommands,Whole.returnActions,Bridge.Command.action,Bridge.HostAction.action] using Whole.return_succeeds values hv tiles
  let final := ByteContents.withCoupled mid ⟨Whole.returned values tiles,mid.coupled.done⟩
  have hrun : IrisExecution.run (ByteContentsProtocolHeap.transition (valueProtocolContext family)) (valuePipelineActions tiles actions)
      (retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles)) = .ok final :=
    ByteContentsProtocolHeap.source_protocol_run (valueProtocolContext family) actions (Whole.returnCommands tiles) hs hc hr
  refine ⟨actions,final,hrun,?_,ha,(Whole.returned_properties values hv tiles).1,(Whole.returned_properties values hv tiles).2.1,
    (fun lane slot index => retry_data_value_output_of_run (next := mid) ht hb hs hcut lane slot index),
    (fun bid hbid => ⟨Whole.returned_can_reclaim values hv tiles bid hbid,fun value => Whole.returned_can_write values hv tiles bid value hbid⟩),
    ByteContentsProtocolHeap.script_adequate _ _ _ _ hrun,
    ByteContentsProtocolHeap.run_projects _ _ hrun⟩
  exact congrArg₂ Bridge.State.mk rfl hcut

theorem retry_value_pipeline_active_blocks_host (a b tiles schedules frame values) (hv : values.length = 10)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) {actions state loc node mode target region}
    (hr : IrisExecution.run (ByteContentsProtocolHeap.transition (valueProtocolContext (retryDataFamily a b tiles schedules))) actions
      (retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles)) = .ok state)
    (hheld : get? (ByteContents.erase state).bytes (ByteAuthority.key loc) = some (.held node mode))
    (hl : Whole.layout tiles target = some region) (hcontains : region.Contains loc) :
    ByteContentsProtocolHeap.transition (valueProtocolContext (retryDataFamily a b tiles schedules)) (.protocol (.host (.reclaim target))) state =
        .error (.authority (.protocolFailure .outstandingLoan)) ∧
      ∀ value, ByteContentsProtocolHeap.transition (valueProtocolContext (retryDataFamily a b tiles schedules)) (.protocol (.host (.write target value))) state =
        .error (.authority (.protocolFailure .outstandingLoan)) := by
  let family := retryDataFamily a b tiles schedules
  have hw := retry_data_source a b tiles schedules (dataRepresentedInitial a b tiles frame) ht hb
  have hc := retry_data_complete a b tiles schedules ht hb
  have hd := retry_data_descriptors a b tiles schedules ht hb
  have hp : ∀ k owner, get? (ByteContents.erase (retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles))).bytes k = some owner → owner = .available := by
    intro k owner hg
    change get? (Iris.Std.PartialMap.map ByteContents.Payload.owner _) k = some owner at hg
    rw [get?_map] at hg
    cases hv : get? (retryValueInitialState a b tiles schedules frame (Whole.prepared values tiles)).cells k with
    | none => simp [hv] at hg
    | some payload =>
      have he : payload.owner = owner := by simpa only [hv,Option.map_some,Option.some.injEq] using hg
      rw [← he]
      exact ByteContents.initialCells_owner_available hv
  have hs := ByteContentsProtocolHeap.run_projects (valueProtocolContext family) actions hr
  have hg := ByteAuthority.active_byte_protects_host_region family values hv ht hb hw hc hd hp hs hheld hl hcontains
  exact ⟨ByteContents.executeCommand_error (ByteAuthority.execute_host_error hg.1),
    fun value => ByteContents.executeCommand_error (ByteAuthority.execute_host_error (hg.2 value))⟩

end
end Ptx.Kernels.HopperDoubleBuffer
