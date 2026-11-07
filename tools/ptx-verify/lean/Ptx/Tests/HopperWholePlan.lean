import Ptx.Kernels.HopperDoubleBufferWholeExecution
import Ptx.Kernels.HopperDoubleBufferWholeInventory

/-! One public protocol for all ten regions, actual source coupling, precise
final-event boundaries and omitted/aliased-region counterexamples. -/
namespace Ptx.HopperWholePlanTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section

abbrev values : List Nat := [0,0,17,19,0,0,0,0,101,103]

theorem public_prepare_for_every_tile_count (tiles : Nat) :
    Ptx.Async.run (Ptx.Async.initial 1 values) (Whole.prepareActions tiles) = .ok (Whole.prepared values tiles) :=
  Whole.preparation_succeeds values rfl tiles

theorem public_complete_client_for_every_tile_count (tiles : Nat) :
    Ptx.Async.run (Ptx.Async.initial 1 values) (Whole.prepareActions tiles ++ Whole.returnActions tiles) = .ok (Whole.returned values tiles) :=
  Whole.complete_public_client values rfl tiles

theorem every_tile_count_returns_all_ten_regions (tiles : Nat) : Ptx.Async.Drain.Returned (Whole.returned values tiles) :=
  (Whole.returned_properties values rfl tiles).1

theorem any_region_can_be_reclaimed (tiles : Nat) (bid : Fin 10) :
    ∃ next, Ptx.Async.reclaim (Whole.returned values tiles) bid = .ok next := Whole.returned_can_reclaim values rfl tiles bid bid.isLt

theorem any_region_can_be_reused (tiles : Nat) (bid : Fin 10) (value : Nat) :
    ∃ next, Ptx.Async.hostWrite (Whole.returned values tiles) bid value = .ok next := Whole.returned_can_write values rfl tiles bid value bid.isLt

theorem four_tiles_have_twenty_six_commands :
    (Whole.prepared values 4).streams[0]?.map (fun stream => stream.queue.length) = some 26 := by decide

theorem four_tiles_have_thirty_four_loans :
    ((Whole.prepared values 4).buffers.map (fun buffer => buffer.loans.length)).sum = 34 := by decide

theorem output_root_has_ticket_twenty_five :
    (Whole.prepared values 4).buffers[8]?.map Ptx.Async.Buffer.loans = some [⟨⟨0,25⟩,.write⟩] := by decide

theorem barrier_root_has_ticket_twenty_six :
    (Whole.prepared values 4).buffers[9]?.map Ptx.Async.Buffer.loans = some [⟨⟨0,26⟩,.write⟩] := by decide

theorem four_tiles_complete_clock :
    (Whole.returned values 4).streams[0]?.map (fun stream => (stream.issued,stream.completed,stream.queue)) = some (26,26,[]) := by decide

theorem four_tiles_leave_no_loans :
    (Whole.returned values 4).buffers.map Ptx.Async.Buffer.loans = List.replicate 10 [] := by decide

theorem opaque_roots_do_not_invent_output_or_resource_values :
    (Whole.returned values 4).buffers.map Ptx.Async.Buffer.value = [0,0,17,19,17,19,17,19,101,103] := by decide

theorem ninety_tiles_return_symbolically : Ptx.Async.Drain.Returned (Whole.returned values 90) := every_tile_count_returns_all_ten_regions 90

theorem source_data_family_complete_coupled_run (a b tiles schedules) (frame : Location → Symbolic.Byte) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Bridge.Steps HopperStage.block Tma.localShared (retryDataCandidate a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster (Whole.plan (retryDataFamily a b tiles schedules))
      ⟨Whole.prepared values tiles,fun _ => False⟩ ⟨Whole.returned values tiles,Present (retryDataCandidate a b tiles schedules)⟩ :=
  Whole.complete_coupled_run (retryDataFamily a b tiles schedules) ht hb
    (retry_data_complete_components a b tiles schedules frame ht hb).1 values rfl

theorem actual_byte_inventory_fully_covered (a b tiles schedules) (frame : Location → Symbolic.Byte) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    {node loc} (ha : Unified.Accesses Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) node loc) :
    ∃ binding ∈ Whole.bindings (retryDataFamily a b tiles schedules), binding.region.Contains loc := by
  have htma := (retry_data_complete_components a b tiles schedules frame ht hb).1
  exact Whole.actual_access_covered (retryDataFamily a b tiles schedules) ht hb htma.source htma.complete htma.descriptors ha

theorem actual_resource_inventory_fully_covered (a b tiles schedules) (frame : Location → Symbolic.Byte) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    {origin event offset} (he : Tma.resourceAt Tma.localShared (retryDataCandidate a b tiles schedules).view origin = some event) (ho : offset < 8) :
    ∃ binding ∈ Whole.bindings (retryDataFamily a b tiles schedules), binding.work = .kernel ∧ binding.mode = .write ∧ binding.region.Contains (event.location.add offset) := by
  have htma := (retry_data_complete_components a b tiles schedules frame ht hb).1
  exact Whole.actual_resource_storage_covered (retryDataFamily a b tiles schedules) ht hb htma.source htma.complete htma.descriptors he ho

theorem one_missing_root_device_step_rejected :
    Ptx.Async.run (Whole.prepared values 4) (List.replicate 25 (.device 0) ++ [.acquire 0]) = .error .notComplete := by decide

theorem async_only_completion_cannot_reclaim_output :
    Ptx.Async.run (Whole.prepared values 4) (List.replicate 24 (.device 0) ++ [.reclaim 8]) = .error .outstandingLoan := by decide

def oldFrontierClient : List Ptx.Async.Action :=
  (((List.range 4).flatMap tileRequests).map Ptx.Async.Preparation.Request.action ++ [.record 0 7]) ++
    [.access 0 8 .write,.access 0 9 .write] ++ List.replicate 26 (.device 0) ++ [.acquire 7]

theorem old_async_frontier_keeps_both_root_loans :
    (Ptx.Async.run (Ptx.Async.initial 1 values) oldFrontierClient).toOption.map
      (fun state => (state.buffers[8]?.map Ptx.Async.Buffer.loans,state.buffers[9]?.map Ptx.Async.Buffer.loans)) =
      some (some [⟨⟨0,25⟩,.write⟩],some [⟨⟨0,26⟩,.write⟩]) := by decide

theorem old_async_frontier_cannot_reclaim_barrier :
    Ptx.Async.run (Ptx.Async.initial 1 values) (oldFrontierClient ++ [.reclaim 9]) = .error .outstandingLoan := by decide

theorem aliased_output_barrier_layout_rejected :
    ¬Regions.Separated (fun bid => [outputStorageRegion,outputStorageRegion][bid]?) := by
  intro hsep
  exact hsep 0 1 outputStorageRegion outputStorageRegion rfl rfl (by decide) ⟨.global,8192⟩
    ⟨rfl,by decide,by decide⟩ ⟨rfl,by decide,by decide⟩

end
end Ptx.HopperWholePlanTests
