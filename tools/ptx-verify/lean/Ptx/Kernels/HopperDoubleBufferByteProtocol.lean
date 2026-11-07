import Ptx.Kernels.HopperDoubleBufferByteIris
import Ptx.Iris.ByteProtocol

/-! One native GenHeap script for actual source-byte claims/retirements,
source-matched device completion and final host acquire. Public preparation
is still justified by its separately checked original interpreter run.
Controller/byte cells contain protocol/permission metadata, not GPU values.
-/
namespace Ptx.Kernels.HopperDoubleBuffer.Whole
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris.ProgramLogic
noncomputable section

def bytePipelineActions {tiles candidate} (family : ReplySourceFamily tiles candidate) (nodes : List Unified.ControlNode) :=
  Ptx.ByteAuthorityHeap.sourceActions (byteContext family) (byteLocations family) nodes ++
    Ptx.ByteAuthorityHeap.protocolActions (returnCommands tiles)

theorem complete_byte_pipeline_witness {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) (retryHistories family))
    (values : List Nat) (hv : values.length = 10) :
    ∃ nodes, ByteAuthority.Footprint.Ordered HopperStage.block candidate (retryHistories family) (fun _ => False) nodes (Present candidate) ∧
      Ptx.IrisExecution.run (Ptx.ByteAuthorityHeap.transition (byteContext family)) (bytePipelineActions family nodes)
        (ByteAuthority.Footprint.initialized ⟨prepared values tiles,fun _ => False⟩ (byteLocations family)) =
        .ok (ByteAuthority.Footprint.initialized ⟨returned values tiles,Present candidate⟩ (byteLocations family)) ∧
      adequate .NotStuck (Ptx.ByteAuthorityHeap.script (byteContext family) (bytePipelineActions family nodes))
        (ByteAuthority.Footprint.initialized ⟨prepared values tiles,fun _ => False⟩ (byteLocations family))
        (fun value _ => value = .ok (ByteAuthority.Footprint.initialized ⟨returned values tiles,Present candidate⟩ (byteLocations family))) := by
  obtain ⟨nodes,ho⟩ := ByteAuthority.Footprint.reached_ordered
    (retry_family_full_prefix family ht hb htma.source htma.histories_valid)
  have hbound := byte_inventory_bounded family ht hb htma.source htma.complete htma.descriptors
  have hc := plan_full_completed family ht hb htma
  have hr : Ptx.Async.run (prepared values tiles) ((returnCommands tiles).map Bridge.Command.action) = .ok (returned values tiles) := by
    simpa [returnCommands,returnActions,Bridge.Command.action,Bridge.HostAction.action] using return_succeeds values hv tiles
  exact ⟨nodes,ho,
    Ptx.ByteAuthorityHeap.source_protocol_run (byteContext family) (byteLocations family) (prepared values tiles) (returned values tiles)
      hbound ho (returnCommands tiles) hc hr,
    Ptx.ByteAuthorityHeap.source_protocol_adequate (byteContext family) (byteLocations family) (prepared values tiles) (returned values tiles)
      hbound ho (returnCommands tiles) hc hr⟩

theorem byte_pipeline_run_is_authority_execution {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (values : List Nat) {nodes final}
    (hr : Ptx.IrisExecution.run (Ptx.ByteAuthorityHeap.transition (byteContext family)) (bytePipelineActions family nodes)
      (ByteAuthority.Footprint.initialized ⟨prepared values tiles,fun _ => False⟩ (byteLocations family)) = .ok final) :
    ByteAuthority.Steps HopperStage.block candidate (retryHistories family) dataCluster (plan family)
      (ByteAuthority.Footprint.initialized ⟨prepared values tiles,fun _ => False⟩ (byteLocations family)) final :=
  Ptx.ByteAuthorityHeap.run_is_steps (byteContext family) (bytePipelineActions family nodes) hr

theorem byte_pipeline_run_projects {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (values : List Nat) {nodes final}
    (hr : Ptx.IrisExecution.run (Ptx.ByteAuthorityHeap.transition (byteContext family)) (bytePipelineActions family nodes)
      (ByteAuthority.Footprint.initialized ⟨prepared values tiles,fun _ => False⟩ (byteLocations family)) = .ok final) :
    Bridge.Steps HopperStage.block Tma.localShared candidate (retryHistories family) dataCluster (plan family)
      ⟨prepared values tiles,fun _ => False⟩ final.coupled :=
  Ptx.ByteAuthorityHeap.run_projects (byteContext family) (bytePipelineActions family nodes) hr

theorem native_active_byte_blocks_host_commands {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (values : List Nat) (hv : values.length = 10) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    {actions state loc node mode target region}
    (hr : Ptx.IrisExecution.run (Ptx.ByteAuthorityHeap.transition (byteContext family)) actions
      (ByteAuthority.Footprint.initialized ⟨prepared values tiles,fun _ => False⟩ (byteLocations family)) = .ok state)
    (hheld : Iris.Std.PartialMap.get? state.bytes (ByteAuthority.key loc) = some (.held node mode))
    (hl : layout tiles target = some region) (hcontains : region.Contains loc) :
    Ptx.ByteAuthorityHeap.transition (byteContext family) (.protocol (.host (.reclaim target))) state =
        .error (.protocolFailure .outstandingLoan) ∧
      ∀ value, Ptx.ByteAuthorityHeap.transition (byteContext family) (.protocol (.host (.write target value))) state =
        .error (.protocolFailure .outstandingLoan) := by
  have hs := Ptx.ByteAuthorityHeap.run_is_steps (byteContext family) actions hr
  have hpool := ByteAuthority.Footprint.initialized_available (⟨prepared values tiles,fun _ => False⟩ : Bridge.State) (byteLocations family)
  have hg := ByteAuthority.active_byte_protects_host_region family values hv ht hb hw hc hd
    (pool := (ByteAuthority.Footprint.initialized ⟨prepared values tiles,fun _ => False⟩ (byteLocations family)).bytes)
    hpool hs hheld hl hcontains
  exact ⟨ByteAuthority.execute_host_error (candidate := candidate) (histories := retryHistories family) (cluster := dataCluster)
    (plan := plan family) (state := state) hg.1,
    fun value => ByteAuthority.execute_host_error (candidate := candidate) (histories := retryHistories family) (cluster := dataCluster)
      (plan := plan family) (state := state) (hg.2 value)⟩

end
end Ptx.Kernels.HopperDoubleBuffer.Whole
