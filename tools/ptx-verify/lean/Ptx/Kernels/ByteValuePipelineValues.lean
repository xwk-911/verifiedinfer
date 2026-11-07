import Ptx.Kernels.ByteValuePipelineAccesses

/-! Available-pool execution through two distinct real memory events. The
reader's values come from the actual preceding write; an independent load reply
still has to pass the original value check after all permissions are acquired.
-/
namespace Ptx.Kernels.ByteValuePipeline
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def oldValues : Location → Option Symbolic.Byte := fun _ => some (.bits (byte 0))
def locations := (demands .write).map ByteAuthority.Footprint.Demand.location
def initialState : ByteContents.State := ⟨⟨Ptx.Async.initial 0 [],fun _ => False⟩,ByteContents.initialCells locations initial⟩
def writerGranted (value reply : Nat) := ByteContentsHeap.granted initialState writerControl (demands .write) oldValues
def afterWriter (value reply : Nat) := ByteContents.finished (candidate value reply) writerMemory (demands .write) (writerGranted value reply)
def writtenValues (value reply : Nat) := ByteContentsHeap.returnedValues (candidate value reply) writerMemory oldValues
def readerGranted (value reply : Nat) := ByteContentsHeap.granted (afterWriter value reply) readerControl (demands .read) (writtenValues value reply)
def afterReader (value reply : Nat) := ByteContents.finished (candidate value reply) readerMemory (demands .read) (readerGranted value reply)
def actions := ByteContentsHeap.cycleActions writerMemory (demands .write) ++ ByteContentsHeap.cycleActions readerMemory (demands .read)

theorem initial_pool_free : ByteContentsHeap.Free initialState (demands .write) oldValues := by
  intro demand hm
  exact ByteContents.initialCells_member (List.mem_map.mpr ⟨demand,hm,rfl⟩)

theorem initial_empty_frame (node : Unified.ControlNode) : ByteAuthority.Footprint.Frame (ByteContents.erase initialState) node [] := by
  apply ByteContents.available_control_frame
  intro k payload hg
  exact ByteContents.initialCells_owner_available hg

theorem writer_permissions_finish (value reply : Nat) :
    ByteAuthority.Footprint.finish .one (candidate value reply) (fun _ => []) writerControl (demands .write) (ByteContents.erase (writerGranted value reply)) =
      .ok (ByteAuthority.retired (ByteContents.erase (writerGranted value reply)) writerControl) := by
  apply ByteAuthority.Footprint.finish_succeeds
  · change ByteAuthority.Ready _ _ _ (ByteContentsHeap.granted _ _ _ _).coupled.done _
    rw [ByteContentsHeap.granted_coupled]
    exact writer_ready value reply
  · exact writer_footprint_sound value reply
  · exact writer_footprint_covers value reply
  · exact footprint_distinct _
  · exact ByteContentsHeap.matches_held (ByteContentsHeap.granted_matches initialState writerControl _ oldValues (footprint_distinct _))
  · exact ByteContentsHeap.granted_frame (initial_empty_frame _)

theorem writer_finishes (value reply : Nat) :
    ByteContents.finish .one (candidate value reply) (fun _ => []) writerMemory (demands .write) (writerGranted value reply) = .ok (afterWriter value reply) := by
  apply ByteContents.finish_succeeds (writer_permissions_finish value reply) (ByteContents.ordinary_linked (writer_view value reply))
  intro loc byteValue hr
  cases hr

theorem writer_cycle_runs (value reply : Nat) :
    IrisExecution.run (ByteContentsHeap.transition (context value reply)) (ByteContentsHeap.cycleActions writerMemory (demands .write)) initialState = .ok (afterWriter value reply) :=
  ByteContentsHeap.cycle_run (context value reply) _ _ _ _ oldValues (writer_ready value reply) (writer_footprint_sound value reply)
    (footprint_distinct _) initial_pool_free (writer_finishes value reply)

theorem returned_writer_pool (value reply : Nat) : ByteContentsHeap.Free (afterWriter value reply) (demands .write) (writtenValues value reply) :=
  ByteContentsHeap.finish_free (ctx := context value reply) (writer_finishes value reply)
    (ByteContentsHeap.granted_matches _ _ _ _ (footprint_distinct _))

theorem reader_pool_comes_from_writer (value reply : Nat) : ByteContentsHeap.Free (afterWriter value reply) (demands .read) (writtenValues value reply) := by
  intro demand hm
  obtain ⟨offset,rfl⟩ := List.mem_ofFn.mp hm
  exact returned_writer_pool value reply ⟨base.add offset.val,.write⟩ (ByteAuthority.Footprint.span_member _ _ _ offset)

theorem reader_granted_ready (value reply : Nat) : ByteAuthority.Ready .one (candidate value reply) (fun _ => []) (readerGranted value reply).coupled.done readerControl := by
  change ByteAuthority.Ready _ _ _ (ByteContentsHeap.granted _ _ _ _).coupled.done _
  rw [ByteContentsHeap.granted_coupled]
  change ByteAuthority.Ready _ _ _ (fun n => (writerGranted value reply).coupled.done n ∨ n = writerControl) _
  have hc := ByteContentsHeap.granted_coupled initialState writerControl (demands .write) oldValues
  change (writerGranted value reply).coupled = initialState.coupled at hc
  rw [hc]
  exact reader_ready_after_writer value reply

theorem reader_permissions_finish (value reply : Nat) :
    ByteAuthority.Footprint.finish .one (candidate value reply) (fun _ => []) readerControl (demands .read) (ByteContents.erase (readerGranted value reply)) =
      .ok (ByteAuthority.retired (ByteContents.erase (readerGranted value reply)) readerControl) := by
  apply ByteAuthority.Footprint.finish_succeeds (reader_granted_ready value reply) (reader_footprint_sound value reply)
    (reader_footprint_covers value reply) (footprint_distinct _)
    (ByteContentsHeap.matches_held (ByteContentsHeap.granted_matches _ _ _ _ (footprint_distinct _)))
  apply ByteContentsHeap.granted_frame
  apply ByteContents.finish_preserves_empty_frame (writer_finishes value reply)
  exact ByteContentsHeap.granted_frame_other (footprint_distinct _) (by decide) (initial_empty_frame readerControl)

theorem reader_value_view_is_actual_write (value : Nat) : ByteContents.Reads (candidate value value) readerMemory (readerGranted value value) := by
  intro loc byteValue hr
  have hu : ByteAuthority.Uses (candidate value value) readerControl loc .read := ⟨.kernel,.kernel (ordinary_read_use hr)⟩
  obtain ⟨demand,hd,he,_⟩ := reader_footprint_covers value value loc .read hu
  have hm : ByteContentsHeap.Matches (readerGranted value value) readerControl (demands .read) (writtenValues value value) :=
    ByteContentsHeap.granted_matches (afterWriter value value) readerControl (demands .read) (writtenValues value value) (footprint_distinct _)
  have hw : ByteContents.writeByte (candidate value value) writerMemory loc = some byteValue := (written_and_read_payloads_match value loc).symm.trans hr
  unfold ByteContents.valueAt
  rw [← he,hm demand hd]
  change (ByteContents.writeByte (candidate value value) writerMemory demand.location).or (oldValues demand.location) = some byteValue
  rw [he,hw]
  rfl

theorem reader_finishes (value : Nat) :
    ByteContents.finish .one (candidate value value) (fun _ => []) readerMemory (demands .read) (readerGranted value value) = .ok (afterReader value value) :=
  ByteContents.finish_succeeds (reader_permissions_finish value value) (ByteContents.ordinary_linked (reader_view value value)) (reader_value_view_is_actual_write value)

theorem reader_cycle_runs (value : Nat) :
    IrisExecution.run (ByteContentsHeap.transition (context value value)) (ByteContentsHeap.cycleActions readerMemory (demands .read)) (afterWriter value value) = .ok (afterReader value value) :=
  ByteContentsHeap.cycle_run (context value value) _ _ _ _ (writtenValues value value) (reader_ready_after_writer value value)
    (reader_footprint_sound value value) (footprint_distinct _) (reader_pool_comes_from_writer value value) (reader_finishes value)

theorem actual_two_event_value_script (value : Nat) :
    IrisExecution.run (ByteContentsHeap.transition (context value value)) actions initialState = .ok (afterReader value value) := by
  rw [actions,IrisExecution.run_append,writer_cycle_runs]
  exact reader_cycle_runs value

end
end Ptx.Kernels.ByteValuePipeline
