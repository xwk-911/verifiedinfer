import Ptx.Hopper.TmaRetryErasure

/-! Pure resource-protocol boundary tests across invalidation/reinitialization.
These raw histories are not claimed source inventories or HistoryValid
candidates. Source-matched retry history witnesses are checked separately. -/
namespace Ptx.HopperRetryLifetimeTests
open Ptx.ISA Ptx.Hopper
noncomputable section

def event (serial : Nat) : Ptx.Event.EventId := ⟨⟨.zero,.zero⟩,serial⟩
def firstCopy : Tma.CopyId := ⟨event 2⟩
def secondCopy : Tma.CopyId := ⟨event 9⟩
def reused : List Tma.Entry := [
  ⟨.source (event 0),.init 1⟩,⟨.source (event 1),.arriveExpectTx 2048⟩,
  ⟨.source (event 3),.tryWaitParity 0 false⟩,⟨.notification firstCopy,.completeTx 2048⟩,
  ⟨.source (event 4),.tryWaitParity 0 true⟩,⟨.source (event 5),.inval⟩,
  ⟨.source (event 6),.init 1⟩,⟨.source (event 7),.tryWaitParity 0 false⟩,
  ⟨.source (event 8),.arriveExpectTx 256⟩,⟨.notification secondCopy,.completeTx 256⟩,
  ⟨.source (event 10),.tryWaitParity 0 true⟩,⟨.source (event 11),.inval⟩]

theorem two_lifetimes_protocol : Mbarrier.run none (reused.map Tma.Entry.operation) = some none := by decide
theorem first_notice_stamp : Tma.stampBefore reused 3 = some ⟨1,0⟩ := by decide
theorem second_wait_stamp : Tma.stampBefore reused 10 = some ⟨2,1⟩ := by decide

theorem old_lifetime_notice_rejected : Tma.observation reused 3 10 = none :=
  Tma.observation_no_reinitialized_object (by decide)

theorem erasure_retains_both_lifetimes :
    Tma.lifetimeBefore (Tma.RetryErasure.erase reused) (Tma.RetryErasure.rank reused 3) = 1 ∧
      Tma.lifetimeBefore (Tma.RetryErasure.erase reused) (Tma.RetryErasure.rank reused 10) = 2 := by
  rw [Tma.RetryErasure.lifetime_erased,Tma.RetryErasure.lifetime_erased]
  decide

theorem erasure_keeps_old_notice_rejected :
    Tma.observation (Tma.RetryErasure.erase reused) (Tma.RetryErasure.rank reused 3) (Tma.RetryErasure.rank reused 10) = none := by
  rw [Tma.RetryErasure.observation_erased_eq (noticeIndex := 3) (waitIndex := 10) (copy := firstCopy)
    (event := event 10) (count := 2048) (parity := 0) ⟨none,two_lifetimes_protocol⟩ (by decide) (by decide) (by decide)]
  exact old_lifetime_notice_rejected

theorem current_lifetime_notice_observed : Tma.observation reused 9 10 = some (secondCopy,event 10) := by decide

theorem erasure_keeps_current_notice_observed :
    Tma.observation (Tma.RetryErasure.erase reused) (Tma.RetryErasure.rank reused 9) (Tma.RetryErasure.rank reused 10) =
      some (secondCopy,event 10) := by
  rw [Tma.RetryErasure.observation_erased_eq (noticeIndex := 9) (waitIndex := 10) (copy := secondCopy)
    (event := event 10) (count := 256) (parity := 0) ⟨none,two_lifetimes_protocol⟩ (by decide) (by decide) (by decide)]
  exact current_lifetime_notice_observed

end
end Ptx.HopperRetryLifetimeTests
