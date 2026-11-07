import Ptx.Kernels.HopperDoubleBufferByteExecution
import Ptx.Iris.ByteSourceExecution

/-! Closed native GenHeap adequacy for the full actual source-authority
prefix. The public protocol remains at its prepared state during this prefix;
the separate byte-authority lift also covers its subsequent drain/acquire.
Neither result is GPU value/runtime refinement or native host/device adequacy.
-/
namespace Ptx.Kernels.HopperDoubleBuffer.Whole
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris.ProgramLogic
noncomputable section

def byteContext {tiles candidate} (family : ReplySourceFamily tiles candidate) : Ptx.ByteAuthorityHeap.Context :=
  {block := HopperStage.block,candidate := candidate,histories := retryHistories family,cluster := dataCluster,plan := plan family}

theorem complete_source_native_witness {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) (retryHistories family))
    (values : List Nat) :
    ∃ nodes, ByteAuthority.Footprint.Ordered HopperStage.block candidate (retryHistories family) (fun _ => False) nodes (Present candidate) ∧
      Ptx.IrisExecution.run (Ptx.ByteAuthorityHeap.transition (byteContext family))
        (Ptx.ByteAuthorityHeap.sourceActions (byteContext family) (byteLocations family) nodes)
        (ByteAuthority.Footprint.initialized ⟨prepared values tiles,fun _ => False⟩ (byteLocations family)) =
        .ok (ByteAuthority.Footprint.initialized ⟨prepared values tiles,Present candidate⟩ (byteLocations family)) ∧
      adequate .NotStuck (Ptx.ByteAuthorityHeap.script (byteContext family)
        (Ptx.ByteAuthorityHeap.sourceActions (byteContext family) (byteLocations family) nodes))
        (ByteAuthority.Footprint.initialized ⟨prepared values tiles,fun _ => False⟩ (byteLocations family))
        (fun value _ => value = .ok (ByteAuthority.Footprint.initialized ⟨prepared values tiles,Present candidate⟩ (byteLocations family))) :=
  Ptx.ByteAuthorityHeap.reached_native_witness (byteContext family) (byteLocations family) (prepared values tiles)
    (byte_inventory_bounded family ht hb htma.source htma.complete htma.descriptors)
    (retry_family_full_prefix family ht hb htma.source htma.histories_valid)

end
end Ptx.Kernels.HopperDoubleBuffer.Whole
