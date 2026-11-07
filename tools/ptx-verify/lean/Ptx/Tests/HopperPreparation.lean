import Ptx.Kernels.HopperDoubleBufferPreparedLoans
import Ptx.Tests.HopperAsyncRegions

/-! Parameterized public preparation/loan provenance, zero work, multiple slot
reuses and indexed event freshness beyond the former fixed event labels. -/
namespace Ptx.HopperPreparationTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section

def values : List Nat := [0,0,17,19,0,0,0,0]
abbrev family := HopperProgressTests.family

theorem every_tile_count_prepares (tiles : Nat) :
    Ptx.Async.run (Ptx.Async.initial 1 values) (preparationActions tiles) = .ok (publicPrepared values tiles) :=
  public_preparation_succeeds values (by decide) tiles

theorem every_tile_count_has_unique_events (tiles : Nat) :
    ((publicPrepared values tiles).events.map Ptx.Async.Event.id).Nodup := public_event_ids_unique values (by decide) tiles

theorem final_frontier_is_exact (tiles : Nat) :
    Ptx.Async.getEvent (publicPrepared values tiles) (tiles+1) = .ok ⟨0,6*tiles⟩ := public_final_event values (by decide) tiles

theorem four_tiles_queue_shape : (publicPrepared values 4).streams[0]?.map
    (fun stream => (stream.issued,stream.completed,stream.queue.length)) = some (24,0,24) := by decide
theorem four_tiles_live_loan_count : ((publicPrepared values 4).buffers.map (fun buffer => buffer.loans.length)).sum = 32 := by decide

theorem zero_tiles_queue_empty : (publicPrepared values 0).streams[0]?.map (fun stream => stream.queue) = some [] := by decide
theorem zero_tiles_no_loans : ((publicPrepared values 0).buffers.map Ptx.Async.Buffer.loans) = List.replicate 8 [] := by decide
theorem zero_tiles_distinct_events : (publicPrepared values 0).events.map Ptx.Async.Event.id = [1,0] := by decide
theorem zero_tiles_final_acquire_succeeds : Ptx.Async.await (publicPrepared values 0) 1 = .ok (publicPrepared values 0) := by decide

theorem ninety_tiles_prepare_without_fixed_id_collision :
    Ptx.Async.run (Ptx.Async.initial 1 values) (preparationActions 90) = .ok (publicPrepared values 90) := every_tile_count_prepares 90
theorem ninety_tiles_final_frontier : Ptx.Async.getEvent (publicPrepared values 90) 91 = .ok ⟨0,540⟩ := final_frontier_is_exact 90
theorem former_fixed_final_id_is_unused : 99 ∉ (publicPrepared values 90).events.map Ptx.Async.Event.id := by
  rw [(public_prepared_properties values (by decide) 90).2.2]
  simp

theorem duplicate_final_event_rejected (tiles : Nat) :
    Ptx.Async.record (publicPrepared values tiles) 0 (tiles+1) = .error .duplicateEvent := by
  have hp := public_prepared_properties values (by decide) tiles
  have hmem : tiles+1 ∈ (publicPrepared values tiles).events.map Ptx.Async.Event.id := by rw [hp.2.2]; simp
  obtain ⟨entry,hm,he⟩ := List.mem_map.mp hmem
  have ha : (publicPrepared values tiles).events.any (fun entry => entry.id == tiles+1) = true :=
    List.any_eq_true.mpr ⟨entry,hm,by simp [he]⟩
  have hg : Ptx.Async.getStream (publicPrepared values tiles) 0 = .ok ⟨(asyncCommands tiles).length,0,asyncCommands tiles,[]⟩ := by
    simp [Ptx.Async.getStream_iff,hp.1.1]
  simp [Ptx.Async.record,hg,ha,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

theorem all_generated_bindings_are_borrowed (a b) :
    Regions.Borrowed (asyncBindings (family a b)) (publicPrepared values 3) := public_bindings_borrowed (family a b) values (by decide)

theorem arbitrary_family_borrowed {tiles candidate} (sourceFamily : ReplySourceFamily tiles candidate)
    (initialValues : List Nat) (hv : initialValues.length = 8) :
    Regions.Borrowed (asyncBindings sourceFamily) (publicPrepared initialValues tiles) := public_bindings_borrowed sourceFamily initialValues hv

theorem arbitrary_command_ticket_provenance (tile : Fin 4) :
    Ptx.Async.Holds (publicPrepared values 4) (aBuffer tile) ⟨asyncTicket tile 1,.write⟩ :=
  public_command_loan values (by decide) 4 tile tile.isLt 1 (by rfl) (.copyWrite 2 (aBuffer tile))

theorem arbitrary_reused_slot_reader (tile : Fin 4) :
    Ptx.Async.Holds (publicPrepared values 4) (aBuffer tile) ⟨asyncTicket tile 4,.read⟩ :=
  public_command_loan values (by decide) 4 tile tile.isLt 4 (by rfl) (.useRead (aBuffer tile))

theorem same_slot_keeps_distinct_write_and_read_tickets : aBuffer 1 = aBuffer 3 ∧ asyncTicket 1 1 ≠ asyncTicket 3 4 := by decide

end
end Ptx.HopperPreparationTests
