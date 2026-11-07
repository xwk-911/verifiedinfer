import Ptx.Kernels.HopperDoubleBufferRetryCtaControl
import Ptx.Tests.HopperRetryAdmission

/-! Actual CTA tags, edges and complete TMA control components with retries.
The positive TmaComponents witness uses explicit bits-zero payload agreement;
unified native control and full-memory admission remain separate. -/
namespace Ptx.HopperRetryCtaControlTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev family := HopperRetryAdmissionTests.family
abbrev candidate := HopperRetryAdmissionTests.candidate
abbrev source := HopperRetryAdmissionTests.source_well_formed
abbrev complete := HopperRetryAdmissionTests.source_complete
abbrev descriptors := HopperRetryAdmissionTests.actual_descriptor_admission
def zeroInitial : Location → Symbolic.Byte := fun _ => .bits (byte 0)

theorem actual_cta_indices (value : ℝ) :
    ((family value).reuseCtaId 0 0 true).serial = 17 ∧ ((family value).reuseCtaId 2 0 false).serial = 40 ∧
    ((family value).reuseCtaId 0 2 true).serial = 10 ∧ ((family value).reuseCtaId 2 2 false).serial = 34 ∧
    ((family value).returnCtaId 0 true).serial = 45 ∧ ((family value).returnCtaId 2 false).serial = 40 := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem actual_checkpoint_generations (value : ℝ) (lane : Wgmma.Lane) (n : Fin 4) :
    generations (replyTileCheckpoint 3 lane ((family value).replies lane) ((family value).schedules lane) n).1 = loopGenerations n :=
  reply_checkpoint_generations _ _ _ _ _

theorem actual_initial_tags (value : ℝ) (lane : Wgmma.Lane) (arrival : Bool) :
    (candidate value).view.ctaTag arrival (initialCtaId 3 lane arrival) = some (0,0) :=
  retry_initial_cta_tag (family value) (source value zeroInitial) lane arrival

theorem actual_reuse_tags (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) (arrival : Bool) :
    (candidate value).view.ctaTag arrival ((family value).reuseCtaId tile lane arrival) = some (2,tile.val) :=
  retry_reuse_cta_tag (family value) (source value zeroInitial) tile tile.isLt lane arrival

theorem actual_return_tags (value : ℝ) (lane : Wgmma.Lane) (arrival : Bool) :
    (candidate value).view.ctaTag arrival ((family value).returnCtaId lane arrival) = some (1,0) :=
  retry_return_cta_tag (family value) (source value zeroInitial) lane arrival

theorem actual_arrivals_precede_returns (value : ℝ) (tile : Fin 3) (left right : Wgmma.Lane) :
    Hopper.CTAControl (candidate value).view ((family value).reuseCtaId tile left true) ((family value).reuseCtaId tile right false) ∧
    retryTmaRank (family value) (.source ((family value).reuseCtaId tile left true)) <
      retryTmaRank (family value) (.source ((family value).reuseCtaId tile right false)) := by
  have he : Hopper.CTAControl (candidate value).view ((family value).reuseCtaId tile left true) ((family value).reuseCtaId tile right false) := by
    rw [Hopper.CTAControl,actual_reuse_tags value tile left true,actual_reuse_tags value tile right false]
    exact ⟨rfl,rfl⟩
  exact ⟨he,retry_control_cta_order (family value) (source value zeroInitial) he⟩

theorem other_generation_rejected (value : ℝ) (left right : Wgmma.Lane) :
    ¬Hopper.CTAControl (candidate value).view ((family value).reuseCtaId 0 left true) ((family value).reuseCtaId 2 right false) := by
  rw [Hopper.CTAControl,retry_reuse_cta_tag (family value) (source value zeroInitial) 0 (by decide) left true,
    retry_reuse_cta_tag (family value) (source value zeroInitial) 2 (by decide) right false]
  rintro ⟨_,he⟩
  cases he

theorem other_barrier_rejected (value : ℝ) (left right : Wgmma.Lane) :
    ¬Hopper.CTAControl (candidate value).view (initialCtaId 3 left true) ((family value).reuseCtaId 0 right false) := by
  rw [Hopper.CTAControl,actual_initial_tags value left true,
    retry_reuse_cta_tag (family value) (source value zeroInitial) 0 (by decide) right false]
  rintro ⟨_,he⟩
  cases he

theorem all_tma_control_acyclic (value : ℝ) : Tma.ControlAcyclic (candidate value).view (retryHistories (family value)) :=
  retry_tma_control_acyclic (family value) (by decide) (source value zeroInitial)

theorem actual_payload_agreement (value : ℝ) : Tma.PayloadAgreement (candidate value).view zeroInitial := by
  intro id copy he offset ho
  have hlen := Unified.tma_copy_payload_length (source value zeroInitial) he
  have hz (q : Nat) : ((family value).replies 0).base.tmaBytes q =
      List.replicate (((family value).replies 0).base.tmaBytes q).length (.bits (byte 0)) := by
    change List.replicate (HopperRetryAdmissionTests.descriptors (q-1)).bytes (Symbolic.Byte.bits (byte 0)) =
      List.replicate (List.replicate (HopperRetryAdmissionTests.descriptors (q-1)).bytes (Symbolic.Byte.bits (byte 0))).length (Symbolic.Byte.bits (byte 0))
    rw [List.length_replicate]
  obtain ⟨tile,ht,hrole | hrole⟩ := retry_all_source_copies (family value) (by decide) (source value zeroInitial) id copy he
  all_goals
    have hrep : copy.payload = List.replicate copy.payload.length (.bits (byte 0)) := by
      rw [hrole.2]
      cases tile <;> exact hz _
    have hoff : offset < copy.payload.length := by rw [hlen]; exact ho
    have hv : Tma.byteValue copy.descriptor copy.coordinates zeroInitial offset = .bits (byte 0) := by
      unfold Tma.byteValue
      cases Tma.sourceByte copy.descriptor copy.coordinates offset <;> rfl
    rw [hv,hrep,List.getElem?_eq_getElem (by simpa only [List.length_replicate] using hoff)]
    simp only [List.getElem_replicate]

theorem positive_tma_components (value : ℝ) :
    Unified.TmaComponents code (completeLaunch 3 zeroInitial) (candidate value) Tma.localShared (dataMaps 3) (retryHistories (family value)) :=
  retry_tma_components (family value) (by decide) (source value zeroInitial) (complete value) (descriptors value) (actual_payload_agreement value)

theorem return_to_arrival_path_rejected (value : ℝ) (tile : Fin 3) (left right : Wgmma.Lane) :
    ¬Ptx.Event.Path (Tma.ControlEdge (candidate value).view (retryHistories (family value)))
      (.source ((family value).reuseCtaId tile right false)) (.source ((family value).reuseCtaId tile left true)) := by
  intro hp
  have he : Tma.ControlEdge (candidate value).view (retryHistories (family value))
      (.source ((family value).reuseCtaId tile left true)) (.source ((family value).reuseCtaId tile right false)) :=
    .inr (.inl (actual_arrivals_precede_returns value tile left right).1)
  exact all_tma_control_acyclic value _ (.trans (.single he) hp)

end
end Ptx.HopperRetryCtaControlTests
