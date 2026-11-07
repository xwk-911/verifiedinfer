import Ptx.Kernels.HopperDoubleBufferControlAdmission
import Ptx.Tests.HopperDoubleBufferResourceAdmission

/-! Actual source CTA tags and global-rank boundary checks. A source-backed
notification edge rejects its reversal. This does not admit RF/co or observers. -/
namespace Ptx.HopperDoubleBufferControlAdmissionTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

abbrev a := HopperDoubleBufferDataTests.a
abbrev b := HopperDoubleBufferDataTests.b
def tagAt (tiles : Nat) (lane : Wgmma.Lane) (serial : Nat) (arrival : Bool) :=
  (dataCompleteCandidate a b tiles).view.ctaTag arrival ⟨(ctx tiles lane).id,serial⟩
abbrev ctaEdge (tiles : Nat) (left : Wgmma.Lane) (li : Nat) (right : Wgmma.Lane) (ri : Nat) :=
  Hopper.CTAControl (dataCompleteCandidate a b tiles).view ⟨(ctx tiles left).id,li⟩ ⟨(ctx tiles right).id,ri⟩

theorem initial_tags : tagAt 3 0 3 true = some (0,0) ∧ tagAt 3 127 1 false = some (0,0) := by decide
theorem first_reuse_tags : tagAt 3 0 16 true = some (2,0) ∧ tagAt 3 127 8 false = some (2,0) := by decide
theorem final_reuse_tags : tagAt 3 0 33 true = some (2,2) ∧ tagAt 3 127 22 false = some (2,2) := by decide
theorem second_reuse_tags : tagAt 5 0 53 true = some (2,4) ∧ tagAt 5 127 36 false = some (2,4) := by decide
theorem output_tags : tagAt 3 0 39 true = some (1,0) ∧ tagAt 3 127 28 false = some (1,0) := by decide
theorem zero_tile_output_tags : tagAt 0 0 9 true = some (1,0) ∧ tagAt 0 127 7 false = some (1,0) := by decide
theorem final_cross_lane_cta_edge : ctaEdge 3 0 33 127 22 := by decide
theorem generation_mismatch_has_no_edge : ¬ctaEdge 3 0 33 127 8 := by decide
theorem barrier_mismatch_has_no_edge : ¬ctaEdge 3 0 39 127 1 := by decide
theorem returning_source_is_not_arrival : tagAt 3 0 34 true = none := by decide
theorem producer_final_gap : producerThreshold 3 = 29 ∧ producerTick 3 28 = 28 ∧ producerTick 3 29 = 32 := by decide
theorem peer_final_gap : peerTick 3 16 = 28 ∧ peerTick 3 17 = 32 ∧ peerTick 3 21 = 36 ∧ peerTick 3 22 = 37 := by decide
theorem zero_tail_gap : producerTick 0 9 = 12 ∧ peerTick 0 6 = 12 := by decide
theorem last_arrival_precedes_first_return :
    sourceControlRank 3 (reuseCtaId a b 3 2 127 true) = 36991 ∧
      sourceControlRank 3 (reuseCtaId a b 3 2 0 false) = 37888 := by decide
theorem implicit_copy_ranks :
    controlRank 3 (.descriptor (dataCopyAId a b 3 0)) = 6272 ∧
      controlRank 3 (.read (dataCopyAId a b 3 0) 0) = 6400 ∧
      controlRank 3 (.write (dataCopyAId a b 3 0) 0) = 6528 ∧
      controlRank 3 (.notify (dataCopyAId a b 3 0)) = 6656 := by decide
theorem notices_precede_waits :
    controlRank 3 (.notify (dataCopyAId a b 3 2)) = 20992 ∧
      sourceControlRank 3 (dataWaitId a b 3 2 127) = 28799 := by decide

theorem source_backed_notice_edge :
    Tma.ResourceEdge (dataHistories a b 3) (.notify (dataCopyAId a b 3 2)) (.source (dataWaitId a b 3 2 127)) := by
  refine ⟨dataGate 0,⟨.notification (dataCopyAId a b 3 2),.completeTx 2048⟩,?_,
    ⟨.source (dataWaitId a b 3 2 127),.tryWaitParity 1 true⟩,?_,?_,rfl,rfl⟩
  · rw [data_histories_at_gate]
    exact List.mem_of_getElem? (data_history_notice_a_at a b 3 0 1 (by decide))
  · rw [data_histories_at_gate]
    exact List.mem_of_getElem? (data_history_wait_at a b 3 0 1 (by decide) 127)
  · rw [data_histories_at_gate]
    exact data_notification_a_before_wait a b 3 0 1 127 (by decide)

theorem reverse_dependency_rejected :
    ¬Tma.ControlEdge (dataCompleteCandidate a b 3).view (dataHistories a b 3)
      (.source (dataWaitId a b 3 2 127)) (.notify (dataCopyAId a b 3 2)) := by
  intro he
  exact data_control_acyclic a b 3 (.notify (dataCopyAId a b 3 2))
    (.trans (.single (Or.inr (Or.inr (Or.inr source_backed_notice_edge)))) (.single he))

theorem arbitrary_real_control (left : TileA) (right : TileB) (tiles : Nat) :
    Tma.ControlAcyclic (dataCompleteCandidate left right tiles).view (dataHistories left right tiles) :=
  data_control_acyclic left right tiles

theorem arbitrary_real_tma_components (left : TileA) (right : TileB) (tiles : Nat) (hb : tiles ≤ 2^28) (frame : Location → Symbolic.Byte) :
    Unified.TmaComponents code (completeLaunch tiles (dataRepresentedInitial left right tiles frame))
      (dataCompleteCandidate left right tiles) Tma.localShared (dataMaps tiles) (dataHistories left right tiles) :=
  data_tma_components left right tiles frame hb

end
end Ptx.HopperDoubleBufferControlAdmissionTests
