import Ptx.Async.AccessLifetime

/-! Lifetime reservations: write-only storage, ordered reuse, independent-stream
conflicts, explicit waits and partial acquisition. These are executable protocol
and universal Lean facts, not GPU data-effect or active-byte-permission claims. -/
namespace Ptx.AccessLifetimeTests
open Ptx.Async

abbrev one := initial 1 [7]
abbrev two := initial 2 [7]

theorem output_without_dummy_input (value : Nat) :
    ∃ final, run (initial 1 [value]) [.access 0 0 .write,.record 0 0,.device 0,.acquire 0] = .ok final ∧
      Drain.Returned final ∧ Preparation.Live final := by
  obtain ⟨final,hr,hreturned,hlive,_⟩ := AccessLifetime.client_returns [value] [.access 0 .write]
    (by intro request hr; simp only [List.mem_singleton] at hr; subst request; change 0 < 1; decide)
  exact ⟨final,hr,hreturned,hlive⟩

theorem arbitrary_write_reuse_returns (value count : Nat) :
    ∃ final, run (initial 1 [value])
      ((List.replicate count (.access 0 0 .write) ++ [.record 0 0]) ++
        (List.replicate count (.device 0) ++ [.acquire 0])) = .ok final ∧ Drain.Returned final := by
  obtain ⟨final,hr,hreturned,_⟩ := AccessLifetime.client_returns [value] (List.replicate count (.access 0 .write))
    (by
      intro request hr
      have heq := (List.mem_replicate.mp hr).2
      subst request
      change 0 < 1
      decide)
  exact ⟨final,by simpa [Preparation.Request.action] using hr,hreturned⟩

theorem read_read_without_order_succeeds :
    (run two [.access 0 0 .read,.access 1 0 .read]).isOk = true := by decide

theorem write_read_without_order_rejected :
    run two [.access 0 0 .write,.access 1 0 .read] = .error .outstandingLoan := by rfl

theorem read_write_without_order_rejected :
    run two [.access 0 0 .read,.access 1 0 .write] = .error .outstandingLoan := by rfl

theorem write_write_without_order_rejected :
    run two [.access 0 0 .write,.access 1 0 .write] = .error .outstandingLoan := by rfl

theorem same_stream_mixed_reservations :
    (run one [.access 0 0 .write,.access 0 0 .read,.access 0 0 .write]).toOption.map
      (fun state => state.buffers[0]?.map Buffer.loans) =
      some (some [⟨⟨0,3⟩,.write⟩,⟨⟨0,2⟩,.read⟩,⟨⟨0,1⟩,.write⟩]) := by decide

theorem queued_write_blocks_reclaim :
    run one [.access 0 0 .write,.reclaim 0] = .error .outstandingLoan := by rfl

theorem queued_write_blocks_host_write :
    run one [.access 0 0 .write,.write 0 9] = .error .outstandingLoan := by rfl

theorem device_completion_does_not_return_loan :
    run one [.access 0 0 .write,.device 0,.reclaim 0] = .error .outstandingLoan := by rfl

theorem acquisition_before_completion_rejected :
    run one [.access 0 0 .write,.record 0 7,.acquire 7] = .error .notComplete := by rfl

theorem old_acquisition_keeps_later_reservation :
    (run one [.access 0 0 .write,.record 0 7,.access 0 0 .write,.device 0,.device 0,.acquire 7]).toOption.map
      (fun state => state.buffers[0]?.map Buffer.loans) = some (some [⟨⟨0,2⟩,.write⟩]) := by decide

theorem old_acquisition_cannot_free_later_write :
    run one [.access 0 0 .write,.record 0 7,.access 0 0 .write,.device 0,.device 0,.acquire 7,.reclaim 0] =
      .error .outstandingLoan := by rfl

theorem cross_stream_dependency_does_not_complete_producer :
    run two [.access 0 0 .write,.record 0 7,.wait 1 7,.access 1 0 .read,.device 1] = .error .notComplete := by rfl

theorem producer_acquire_keeps_consumer_loan :
    run two [.access 0 0 .write,.record 0 7,.wait 1 7,.access 1 0 .read,.device 0,.acquire 7,.reclaim 0] =
      .error .outstandingLoan := by rfl

theorem both_streams_complete_and_acquire_can_reclaim :
    (run two [.access 0 0 .write,.record 0 7,.wait 1 7,.access 1 0 .read,
      .device 0,.device 1,.device 1,.record 1 8,.acquire 7,.acquire 8,.reclaim 0]).toOption.map
      (fun state => state.buffers[0]?.map Buffer.alive) = some (some false) := by decide

theorem opaque_access_does_not_fabricate_output_value :
    (run one [.access 0 0 .write,.record 0 7,.device 0,.acquire 7]).toOption.map
      (fun state => state.buffers[0]?.map Buffer.value) = some (some 7) := by decide

theorem missing_storage_rejected : step (initial 1 []) (.access 0 0 .write) = .error .invalidBuffer := by rfl

theorem freed_storage_rejected : run one [.reclaim 0,.access 0 0 .write] = .error .freed := by rfl

end Ptx.AccessLifetimeTests
