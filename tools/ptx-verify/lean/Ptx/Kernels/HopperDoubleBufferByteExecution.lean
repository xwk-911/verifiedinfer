import Ptx.Hopper.ByteExecution
import Ptx.Kernels.HopperDoubleBufferWholeExecution

/-! Construct byte authority for the entire bounded positive-K source and its
existing public drain/acquire execution. All descriptor, TMA, native, ordinary
and resource uses are bounded by the already checked region inventory.
No initially held byte fragments or per-node availability premise is supplied.
This is a source/control authority lift, not whole-kernel Iris/value adequacy.
-/
namespace Ptx.Kernels.HopperDoubleBuffer.Whole
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def byteLocations {tiles candidate} (family : ReplySourceFamily tiles candidate) : List Location :=
  ByteAuthority.Footprint.bindingLocations (bindings family)

theorem byte_inventory_bounded {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) :
    ByteAuthority.Footprint.Bounded candidate (byteLocations family) := by
  apply ByteAuthority.Footprint.bounded_of_bindings
  intro node loc mode hu
  obtain ⟨work,hu⟩ := hu
  obtain ⟨binding,hm,_,_,hr⟩ := all_uses_covered family ht hb hw hc hd _ _ _ _ hu
  exact ⟨binding,hm,hr⟩

theorem byte_footprints_complete {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (node : Unified.ControlNode) :
    ByteAuthority.Footprint.Sound candidate node (ByteAuthority.Footprint.inventory candidate node (byteLocations family)) ∧
    ByteAuthority.Footprint.Covers candidate node (ByteAuthority.Footprint.inventory candidate node (byteLocations family)) ∧
    ByteAuthority.Footprint.Distinct (ByteAuthority.Footprint.inventory candidate node (byteLocations family)) :=
  ⟨ByteAuthority.Footprint.inventory_sound _ _ _,
    ByteAuthority.Footprint.inventory_covers (byte_inventory_bounded family ht hb hw hc hd node),
    ByteAuthority.Footprint.inventory_distinct _ _ _⟩

theorem lift_public_execution {tiles initial candidate histories before after} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hs : Bridge.Steps HopperStage.block Tma.localShared candidate histories dataCluster (plan family) before after) :
    ByteAuthority.Steps HopperStage.block candidate histories dataCluster (plan family)
      (ByteAuthority.Footprint.initialized before (byteLocations family))
      (ByteAuthority.Footprint.initialized after (byteLocations family)) :=
  ByteAuthority.Footprint.lift_steps (byte_inventory_bounded family ht hb hw hc hd) hs

theorem complete_byte_authority_run {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) (retryHistories family))
    (values : List Nat) (hv : values.length = 10) :
    ByteAuthority.Steps HopperStage.block candidate (retryHistories family) dataCluster (plan family)
      (ByteAuthority.Footprint.initialized ⟨prepared values tiles,fun _ => False⟩ (byteLocations family))
      (ByteAuthority.Footprint.initialized ⟨returned values tiles,Present candidate⟩ (byteLocations family)) :=
  lift_public_execution family ht hb htma.source htma.complete htma.descriptors
    (complete_coupled_run family ht hb htma values hv)

theorem final_byte_authority_available {tiles candidate} (family : ReplySourceFamily tiles candidate) (values : List Nat)
    (loc : Location) (hm : loc ∈ byteLocations family) :
    Iris.Std.PartialMap.get?
      (ByteAuthority.Footprint.initialized ⟨returned values tiles,Present candidate⟩ (byteLocations family)).bytes
      (ByteAuthority.key loc) = some .available := by
  have ha := ByteAuthority.Footprint.pool_available
    (⟨returned values tiles,Present candidate⟩ : Bridge.State) (ByteAuthority.Footprint.locationDemands (byteLocations family))
  exact ha ⟨loc,.read⟩ (List.mem_map.mpr ⟨loc,hm,rfl⟩)

end
end Ptx.Kernels.HopperDoubleBuffer.Whole
