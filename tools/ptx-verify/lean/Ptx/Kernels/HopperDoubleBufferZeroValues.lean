import Ptx.Kernels.HopperDoubleBufferKernelOwnership
import Ptx.Iris.ByteContentsSource
import Ptx.Iris.ByteContentsWrites

/-! Complete checked byte-value scripts for every actual completed zero-K
source candidate. There are no reads/TMA/native collectives, but output stores
and both barriers' opaque storage reservations remain in the actual inventory.
Initial byte values are arbitrary. Native adequacy retains whole-map ownership.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris.ProgramLogic
noncomputable section

def zeroValueContext (candidate : Unified.Candidate) : ByteContentsHeap.Context := ⟨HopperStage.block,candidate,zeroHistories⟩
-- Keep elaboration from evaluating the closed 2064-cell pool during inference.
@[irreducible] def zeroValueLocations := ByteAuthority.Footprint.regionLocations outputStorageRegion ++ ByteAuthority.Footprint.regionLocations barrierStorageRegion
def zeroValueInitialState (_candidate : Unified.Candidate) (initial : Location → Symbolic.Byte) (protocol : Ptx.Async.State) : ByteContents.State :=
  ⟨⟨protocol,fun _ => False⟩,ByteContents.initialCells zeroValueLocations initial⟩

theorem zero_value_uses_are_kernel {initial candidate node loc mode}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (hu : ByteAuthority.Uses candidate node loc mode) : KernelUse Tma.localShared candidate node loc mode := by
  obtain ⟨work,hu⟩ := hu
  cases hu with
  | kernel hu => exact hu
  | async hu =>
    cases mode with
    | read =>
      obtain ⟨value,hread⟩ := use_actual hu
      rw [completed_zero_no_reads hw hc] at hread
      cases hread
    | write =>
      cases hu with
      | tmaWrite hl hv => simp [Tma.transferByte,completed_zero_no_tma hw hc] at hv

theorem zero_value_inventory_bounded {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    ByteAuthority.Footprint.Bounded candidate zeroValueLocations := by
  intro node loc mode hu
  unfold zeroValueLocations
  obtain ⟨index,_,hr⟩ := zero_kernel_use_coverage hw hc node loc mode (zero_value_uses_are_kernel hw hc hu)
  fin_cases index
  · exact List.mem_append.mpr (.inl (ByteAuthority.Footprint.mem_regionLocations hr))
  · exact List.mem_append.mpr (.inr (ByteAuthority.Footprint.mem_regionLocations hr))

theorem zero_value_read_impossible {initial candidate read loc value}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (hr : ByteContents.readByte candidate read loc = some value) : False := by
  change Unified.readByte Tma.localShared Access.globalDescriptor candidate read loc = some value at hr
  rw [completed_zero_no_reads hw hc] at hr
  cases hr

theorem zero_value_write_in_output {initial candidate node loc value}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (he : ByteContents.writeByte candidate node loc = some value) : outputStorageRegion.Contains loc := by
  cases node with
  | wgmmaRead issue operand => rw [ByteContents.writeByte,Unified.native_write_none] at he; cases he
  | base node =>
    cases node with
    | copyRead id | copyWrite id => simp [ByteContents.writeByte,Unified.writeByte,Unified.kind,Access.kind,candidate_no_nonbulk (by decide) hw hc] at he
    | tma node =>
      cases node with
      | source id => exact ordinary_write_in_output (by decide) hw hc he
      | descriptor id | read id offset | write id offset | notify id =>
        simp [ByteContents.writeByte,Unified.writeByte,Unified.kind,Access.kind,Tma.writeLocation,Tma.transferByte,
          completed_zero_no_tma hw hc,Ptx.Event.Kind.writeByte] at he

theorem zero_value_read_frontier {initial candidate}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    ByteContentsHeap.ReadFrontier (zeroValueContext candidate) zeroRf := by
  exact ⟨fun _ _ _ hr => (zero_value_read_impossible hw hc hr).elim,
    fun _ _ _ hr => (zero_value_read_impossible hw hc hr).elim,
    fun _ _ _ hr => (zero_value_read_impossible hw hc hr).elim⟩

theorem zero_value_initial_future {initial candidate protocol}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    ByteContentsHeap.FutureReads (zeroValueContext candidate) (fun _ => initial) zeroRf (zeroValueInitialState candidate initial protocol) := by
  intro read loc value hr
  exact (zero_value_read_impossible hw hc hr).elim

theorem zero_value_output_of_unique_writes {initial candidate next}
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate)
    (hi : ByteContentsHeap.UniqueWrites (zeroValueContext candidate) next) (hcut : next.coupled.done = Present candidate)
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt next ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 0 index.val) := by
  have hwrite := completed_zero_output_byte hw hc lane slot index
  apply hi _ _ _ hwrite
  · intro other written hw'
    exact completed_zero_writers_unique hw hc hw' hwrite
  · rw [hcut]
    exact kernel_use_present (ordinary_write_use hwrite)

theorem zero_value_source_witness {initial candidate} (protocol : Ptx.Async.State)
    (hw : Unified.WellFormed code (completeLaunch 0 initial) candidate) (hc : Unified.Complete candidate) :
    ∃ actions next,
      IrisExecution.run (ByteContentsHeap.transition (zeroValueContext candidate)) actions (zeroValueInitialState candidate initial protocol) = .ok next ∧
      next.coupled.done = Present candidate ∧ next.coupled.protocol = protocol ∧ ByteContentsHeap.Available next ∧
      ByteContentsHeap.Allocated next zeroValueLocations ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4), ByteContents.valueAt next ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) = some (.realPart .f32 0 index.val)) ∧
      adequate .NotStuck (ByteContentsHeap.script (zeroValueContext candidate) actions) (zeroValueInitialState candidate initial protocol) (fun result _ => result = .ok next) := by
  have hm := completed_zero_memory_witness hw hc
  obtain ⟨actions,next,hr,hcut,ha,hl,_⟩ := ByteContentsHeap.reached_value_witness (zeroValueContext candidate) zeroValueLocations
    (zeroValueInitialState candidate initial protocol) hm.toCausalConstraints
    (fun _ _ _ hr => (zero_value_read_impossible hw hc hr).elim) (candidate_no_nonbulk (by decide) hw hc)
    (zero_value_inventory_bounded hw hc) (zero_value_read_frontier hw hc) (zero_value_initial_future hw hc)
    (ByteContentsHeap.initial_cells_available _ _ _) (ByteContentsHeap.initial_cells_allocated _ _ _) rfl
    (full_prefix_reached (completed_zero_history_valid hw hc) (dataNativeControlRank 0) (fun _ _ => completed_zero_control_rank hw hc))
  have hi := ByteContentsHeap.unique_writes_run (zeroValueContext candidate) actions (ByteContentsHeap.unique_writes_initial (by intro _ h; exact h)) hr
  exact ⟨actions,next,hr,hcut,ByteContentsHeap.run_protocol _ _ hr,ha,hl,zero_value_output_of_unique_writes hw hc hi hcut,
    ByteContentsHeap.script_adequate _ _ _ _ hr⟩

end
end Ptx.Kernels.HopperDoubleBuffer
