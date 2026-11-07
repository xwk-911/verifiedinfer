import Ptx.Kernels.HopperDoubleBufferLoanReturn
import Ptx.Tests.HopperPreparation

/-! Generic finite drain/return, concrete zero/multi-reuse executions and
negative waits/early acquisition. All are protocol/model facts, not GPU runs.
-/
namespace Ptx.HopperLoanReturnTests
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section

abbrev values := HopperPreparationTests.values

theorem every_tile_count_finishes (tiles : Nat) :
    Ptx.Async.run (publicPrepared values tiles) (loanReturnActions tiles) = .ok (publicReturned values tiles) :=
  public_return_succeeds values (by decide) tiles

theorem complete_public_client_finishes (tiles : Nat) :
    Ptx.Async.run (Ptx.Async.initial 1 values) (preparationActions tiles ++ loanReturnActions tiles) = .ok (publicReturned values tiles) :=
  complete_lifetime_client_succeeds values (by decide) tiles

theorem every_tile_count_returns_every_loan (tiles : Nat) : Ptx.Async.Drain.Returned (publicReturned values tiles) :=
  (public_returned_properties values (by decide) tiles).1

theorem any_region_can_be_reclaimed (tiles : Nat) (bid : Fin 8) :
    ∃ state, Ptx.Async.reclaim (publicReturned values tiles) bid = .ok state := returned_can_reclaim values (by decide) tiles bid bid.isLt

theorem any_region_can_be_reused (tiles : Nat) (bid : Fin 8) (value : Nat) :
    ∃ state, Ptx.Async.hostWrite (publicReturned values tiles) bid value = .ok state := returned_can_write values (by decide) tiles bid value bid.isLt

theorem zero_drain_keeps_protocol : publicReturned values 0 = publicPrepared values 0 := by decide
theorem four_tiles_complete_clock : (publicReturned values 4).streams[0]?.map (fun stream => (stream.issued,stream.completed,stream.queue)) = some (24,24,[]) := by decide
theorem four_tiles_no_remaining_loans : (publicReturned values 4).buffers.map Ptx.Async.Buffer.loans = List.replicate 8 [] := by decide
theorem four_tiles_both_slots_written : (publicReturned values 4).buffers.map Ptx.Async.Buffer.value = [0,0,17,19,17,19,17,19] := by decide
theorem ninety_tiles_return_symbolically : Ptx.Async.Drain.Returned (publicReturned values 90) := every_tile_count_returns_every_loan 90

theorem acquire_before_device_progress_rejected : Ptx.Async.await (publicPrepared values 4) 5 = .error .notComplete := by decide
theorem one_missing_device_step_rejected :
    Ptx.Async.run (publicPrepared values 4) (List.replicate 23 (.device 0) ++ [.acquire 5]) = .error .notComplete := by decide

def selfWait : Ptx.Async.State := {streams := [⟨1,0,[.wait ⟨0,1⟩],[]⟩],buffers := []}

theorem wait_queue_is_not_plain : ¬Ptx.Async.Drain.Plain [.wait ⟨0,1⟩] := by
  intro hp
  exact hp (.wait ⟨0,1⟩) (by simp) ⟨0,1⟩ rfl

theorem self_wait_blocks_progress : Ptx.Async.deviceStep selfWait 0 = .error .notComplete := by decide

theorem self_wait_still_has_protocol_invariant : Ptx.Async.Invariant selfWait := by
  refine ⟨?_,?_⟩
  · intro sid stream hg
    cases sid with
    | zero => simp only [selfWait,List.getElem?_cons_zero,Option.some.injEq] at hg; subst stream; rfl
    | succ sid => simp [selfWait] at hg
  · intro sid stream hg index command hc bid mode ha
    cases sid with
    | succ sid => simp [selfWait] at hg
    | zero =>
      simp only [selfWait,List.getElem?_cons_zero,Option.some.injEq] at hg
      subst stream
      cases index with
      | succ index => simp at hc
      | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at hc; subst command; cases ha

theorem arbitrary_data_family_coupled_run (a b tiles schedules) (frame : Location → Symbolic.Byte) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Bridge.Steps HopperStage.block Tma.localShared (retryDataCandidate a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster (asyncPlan (retryDataFamily a b tiles schedules))
      ⟨publicPrepared values tiles,fun _ => False⟩ ⟨publicReturned values tiles,Present (retryDataCandidate a b tiles schedules)⟩ :=
  public_complete_coupled_run (retryDataFamily a b tiles schedules) ht hb
    (retry_data_complete_components a b tiles schedules frame ht hb).1 values (by decide)

end
end Ptx.HopperLoanReturnTests
