import Ptx.Kernels.HopperDoubleBufferRetryCtaControl
import Ptx.Hopper.UnifiedHistoryControl

/-! Source/CTA/TMA paths valid for arbitrary resource histories. These paths
are reconstructed from actual event identities and source order; resource
serialization is not used to assume the paths we later constrain. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_expect_before_copy_a {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) :
    Hopper.ProgramOrder candidate.view (family.expectId tile) (family.copyAId tile).issue := by
  have hs := reply_expect_copy_source_order tiles (family.replies 0) (family.schedules 0) tile
  refine ⟨Hopper.barrier_present (family_expect_at family hw tile ht),?_,hs.1,hs.2.2.1⟩
  have he := Tma.copyAt_iff.mp (family_copy_a_at family hw tile ht)
  simp only [Hopper.Candidate.Present,he,Option.isSome_some]

theorem retry_expect_before_copy_b {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) :
    Hopper.ProgramOrder candidate.view (family.expectId tile) (family.copyBId tile).issue := by
  have hs := reply_expect_copy_source_order tiles (family.replies 0) (family.schedules 0) tile
  refine ⟨Hopper.barrier_present (family_expect_at family hw tile ht),?_,hs.1.trans hs.2.1,hs.2.2.1.trans hs.2.2.2⟩
  have he := Tma.copyAt_iff.mp (family_copy_b_at family hw tile ht)
  simp only [Hopper.Candidate.Present,he,Option.isSome_some]

theorem retry_expect_notification_a_path {tiles initial candidate histories} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (tile : Nat) (ht : tile < tiles) :
    Ptx.Event.Path (Unified.ControlEdge HopperStage.block candidate histories)
      (.base (.source (family.expectId tile))) (.base (.notify (family.copyAId tile))) := by
  have hb : 0 < (replyCopyA tiles (family.replies 0) (family.schedules 0) tile).descriptor.bytes := by
    rw [family_copy_a_descriptor family hw hd tile ht]
    change 0 < 2048
    decide
  exact .trans (.single (Unified.base_control_edge (.inl (show Tma.ProgramOrder candidate.view (.source (family.expectId tile)) (.source (family.copyAId tile).issue) from retry_expect_before_copy_a family hw tile ht))))
    (Unified.tma_issue_notification_path (family_copy_a_at family hw tile ht) hb)

theorem retry_expect_notification_b_path {tiles initial candidate histories} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles))
    (tile : Nat) (ht : tile < tiles) :
    Ptx.Event.Path (Unified.ControlEdge HopperStage.block candidate histories)
      (.base (.source (family.expectId tile))) (.base (.notify (family.copyBId tile))) := by
  have hb : 0 < (replyCopyB tiles (family.replies 0) (family.schedules 0) tile).descriptor.bytes := by
    rw [family_copy_b_descriptor family hw hd tile ht]
    change 0 < 256
    decide
  exact .trans (.single (Unified.base_control_edge (.inl (show Tma.ProgramOrder candidate.view (.source (family.expectId tile)) (.source (family.copyBId tile).issue) from retry_expect_before_copy_b family hw tile ht))))
    (Unified.tma_issue_notification_path (family_copy_b_at family hw tile ht) hb)

theorem retry_wait_resource_at {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) :
    Tma.resourceAt Tma.localShared candidate.view (.source (family.waitId tile lane)) =
      some ⟨dataGate (stage tile),.tryWaitParity (expectedParity tile) true⟩ := by
  apply Hopper.barrierAt_iff.mpr
  rw [Unified.view_eventAt,family_wait_at family hw tile ht lane]
  rfl

theorem retry_wait_before_reuse_cta {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) (lane : Wgmma.Lane) :
    Hopper.ProgramOrder candidate.view (family.waitId tile lane) (family.reuseCtaId tile lane true) := by
  refine ⟨Hopper.barrier_present (retry_wait_resource_at family hw tile ht lane),
    Hopper.cta_tag_present (retry_reuse_cta_tag family hw tile ht lane true),rfl,?_⟩
  change replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+family.schedules lane tile <
    replyTileStart tiles lane (family.replies lane) (family.schedules lane) tile+family.schedules lane tile+
      preludeEventCount tile tiles (HopperStage.leader lane)+5+ctaOffset true
  omega

theorem retry_reuse_cta_before_later_expect_serial {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile next : Nat) (hg : tile+2 ≤ next) : (family.reuseCtaId tile 0 false).serial < (family.expectId next).serial := by
  have hbefore : (family.reuseCtaId tile 0 false).serial < replyTileStart tiles 0 (family.replies 0) (family.schedules 0) (tile+1) := by
    simp only [ReplySourceFamily.reuseCtaId,ctaOffset,Bool.false_eq_true,ite_false,reply_tile_start_succ]
    omega
  cases next with
  | zero => omega
  | succ next =>
    have hm := (reply_tile_start_strict_mono tiles 0 (family.replies 0) (family.schedules 0)).monotone (show tile+1 ≤ next by omega)
    change (family.reuseCtaId tile 0 false).serial < replyTileStart tiles 0 (family.replies 0) (family.schedules 0) next+family.schedules 0 next+1+0
    omega

theorem retry_reuse_cta_before_later_expect {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile next : Nat) (hg : tile+2 ≤ next) (hn : next < tiles) :
    Hopper.ProgramOrder candidate.view (family.reuseCtaId tile 0 false) (family.expectId next) := by
  refine ⟨Hopper.cta_tag_present (retry_reuse_cta_tag family hw tile (by omega) 0 false),
    Hopper.barrier_present (family_expect_at family hw next hn),?_,retry_reuse_cta_before_later_expect_serial family tile next hg⟩
  cases next <;> rfl

theorem retry_wait_later_expect_path {tiles initial candidate histories} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile next : Nat) (hg : tile+2 ≤ next) (hn : next < tiles) (lane : Wgmma.Lane) :
    Ptx.Event.Path (Unified.ControlEdge HopperStage.block candidate histories)
      (.base (.source (family.waitId tile lane))) (.base (.source (family.expectId next))) := by
  have hcta : Hopper.CTAControl candidate.view (family.reuseCtaId tile lane true) (family.reuseCtaId tile 0 false) := by
    rw [Hopper.CTAControl,retry_reuse_cta_tag family hw tile (by omega) lane true,retry_reuse_cta_tag family hw tile (by omega) 0 false]
    exact ⟨rfl,rfl⟩
  exact .trans (.single (Unified.base_control_edge (.inl (show Tma.ProgramOrder candidate.view (.source (family.waitId tile lane)) (.source (family.reuseCtaId tile lane true)) from retry_wait_before_reuse_cta family hw tile (by omega) lane))))
    (.trans (.single (Unified.base_control_edge (.inr (.inl (show Tma.CTAControl candidate.view (.source (family.reuseCtaId tile lane true)) (.source (family.reuseCtaId tile 0 false)) from hcta)))))
      (.single (Unified.base_control_edge (.inl (show Tma.ProgramOrder candidate.view (.source (family.reuseCtaId tile 0 false)) (.source (family.expectId next)) from retry_reuse_cta_before_later_expect family hw tile next hg hn)))))

end
end Ptx.Kernels.HopperDoubleBuffer
