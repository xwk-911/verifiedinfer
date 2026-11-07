import Ptx.Kernels.HopperDoubleBufferRetryHistoryPaths

/-! Necessary phase/prefix bounds for every admitted history of an actual
retry source family. No equality with the constructed retry histories occurs
in these statements. Full phase-stamp/publication identification is separate. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem arbitrary_history_expect_before_a {tiles initial candidate histories} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (tile : Nat) (ht : tile < tiles) :
    Tma.Before (histories (dataGate (stage tile))) (.source (family.expectId tile)) (.notification (family.copyAId tile)) :=
  Unified.history_before_of_control_path (hh _) hc (family_expect_at family hw tile ht) (family_notification_a family hw hd tile ht)
    (retry_expect_notification_a_path family hw hd tile ht)

theorem arbitrary_history_expect_before_b {tiles initial candidate histories} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (tile : Nat) (ht : tile < tiles) :
    Tma.Before (histories (dataGate (stage tile))) (.source (family.expectId tile)) (.notification (family.copyBId tile)) :=
  Unified.history_before_of_control_path (hh _) hc (family_expect_at family hw tile ht) (family_notification_b family hw hd tile ht)
    (retry_expect_notification_b_path family hw hd tile ht)

theorem arbitrary_history_wait_before_later_expect {tiles initial candidate histories} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (tile next : Nat) (hlt : tile < next) (hn : next < tiles)
    (hs : stage tile = stage next) (lane : Wgmma.Lane) :
    Tma.Before (histories (dataGate (stage tile))) (.source (family.waitId tile lane)) (.source (family.expectId next)) := by
  have he : Tma.resourceAt Tma.localShared candidate.view (.source (family.expectId next)) =
      some ⟨dataGate (stage tile),.arriveExpectTx 2304⟩ := by rw [hs]; exact family_expect_at family hw next hn
  exact Unified.history_before_of_control_path (hh _) hc (retry_wait_resource_at family hw tile (by omega) lane) he
    (retry_wait_later_expect_path family hw tile next (retry_same_slot_gap hlt hs) hn lane)

theorem arbitrary_history_notification_a_prefix {tiles initial candidate histories} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (tile : Nat) (ht : tile < tiles) (cut : Nat)
    (hp : Tma.Origin.notification (family.copyAId tile) ∈ ((histories (dataGate (stage tile))).take cut).map Tma.Entry.origin) :
    Tma.Origin.source (family.expectId tile) ∈ ((histories (dataGate (stage tile))).take cut).map Tma.Entry.origin :=
  Tma.before_prefix_closed (arbitrary_history_expect_before_a family hw hd hh hc tile ht) cut hp

theorem arbitrary_history_notification_b_prefix {tiles initial candidate histories} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (tile : Nat) (ht : tile < tiles) (cut : Nat)
    (hp : Tma.Origin.notification (family.copyBId tile) ∈ ((histories (dataGate (stage tile))).take cut).map Tma.Entry.origin) :
    Tma.Origin.source (family.expectId tile) ∈ ((histories (dataGate (stage tile))).take cut).map Tma.Entry.origin :=
  Tma.before_prefix_closed (arbitrary_history_expect_before_b family hw hd hh hc tile ht) cut hp

theorem arbitrary_history_wait_prefix_excludes_later_expect {tiles initial candidate histories} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (histories loc))
    (hc : Unified.ControlAcyclic HopperStage.block candidate histories) (tile next : Nat) (hlt : tile < next) (hn : next < tiles)
    (hs : stage tile = stage next) (lane : Wgmma.Lane) (cut : Nat)
    (hcut : cut ≤ ((histories (dataGate (stage tile))).map Tma.Entry.origin).idxOf (.source (family.waitId tile lane))+1) :
    Tma.Origin.source (family.expectId next) ∉ ((histories (dataGate (stage tile))).take cut).map Tma.Entry.origin :=
  Tma.later_not_in_prefix (arbitrary_history_wait_before_later_expect family hw hh hc tile next hlt hn hs lane) cut hcut

theorem admitted_history_phase_bounds {tiles initial candidate histories} (family : ReplySourceFamily tiles candidate)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) histories)
    (hc : Unified.ControlAdmitted HopperStage.block candidate histories) :
    (∀ tile, tile < tiles →
      Tma.Before (histories (dataGate (stage tile))) (.source (family.expectId tile)) (.notification (family.copyAId tile)) ∧
      Tma.Before (histories (dataGate (stage tile))) (.source (family.expectId tile)) (.notification (family.copyBId tile))) ∧
    (∀ tile next, tile < next → next < tiles → stage tile = stage next → ∀ lane,
      Tma.Before (histories (dataGate (stage tile))) (.source (family.waitId tile lane)) (.source (family.expectId next))) :=
  ⟨fun tile ht => ⟨arbitrary_history_expect_before_a family htma.source htma.descriptors htma.histories_valid hc.2 tile ht,
      arbitrary_history_expect_before_b family htma.source htma.descriptors htma.histories_valid hc.2 tile ht⟩,
    fun tile next hlt hn hs lane => arbitrary_history_wait_before_later_expect family htma.source htma.histories_valid hc.2 tile next hlt hn hs lane⟩

end
end Ptx.Kernels.HopperDoubleBuffer
