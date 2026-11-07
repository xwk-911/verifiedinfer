import Ptx.Kernels.HopperDoubleBufferRetryResourceAdmission
import Ptx.Tests.HopperRetryPrefetch
import Ptx.Hopper.TmaRetryErasure

/-! A source-complete, descriptor-admitted three-tile nonzero-retry fixture.
All resource histories and A/B completion observations are admitted. Native
control, input memory/RF, tensor arithmetic and full launch admission remain
separate; arbitrary captured matrix results are deliberately retained. -/
namespace Ptx.HopperRetryAdmissionTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev schedule := HopperRetryPrefetchTests.schedule
def descriptors (q : Nat) : Tma.Descriptor2D :=
  if q ∈ [0,HopperRetryPrefetchTests.query 0 0+schedule 0 0+1,HopperRetryPrefetchTests.query 0 1+schedule 0 1+1]
    then aView 65536 3 else bView (dataBBase 3) 3
def replies (value : ℝ) (lane : Wgmma.Lane) : Wgmma.Oracle := {HopperRetryPrefetchTests.replies value lane with
  base := {(HopperRetryPrefetchTests.replies value lane).base with
    descriptor := descriptors,tmaBytes := fun q => List.replicate (descriptors (q-1)).bytes (.bits (byte 0))}}
def candidate (value : ℝ) : Unified.Candidate := replyCandidate 3 (replies value) schedule
def family (value : ℝ) : ReplySourceFamily 3 (candidate value) := {
  replies := replies value,schedules := schedule,traces := replyTrace 3 (replies value) schedule
  members := fun lane => List.mem_ofFn.mpr ⟨lane,rfl⟩
  ids := fun _ => rfl,oracles := fun _ => rfl,events := fun _ => rfl
}

theorem source_well_formed (value : ℝ) (initial : Location → Symbolic.Byte) :
    Unified.WellFormed code (completeLaunch 3 initial) (candidate value) := by
  apply reply_candidate_well_formed 3 (replies value) schedule initial (by decide) (by decide)
  · intro lane _
    constructor <;> simp only [replies,List.length_replicate]
  · intro lane tile ht
    obtain ⟨hf,hs⟩ := HopperRetryPrefetchTests.wait_schedule_metadata lane ⟨tile,ht⟩
    refine ⟨hf,hs,?_⟩
    intro _
    constructor <;> simp only [replies,List.length_replicate] <;> congr 2

theorem source_complete (value : ℝ) : Unified.Complete (candidate value) :=
  reply_candidate_complete 3 (replies value) schedule (by decide) (by decide)

theorem actual_descriptor_admission (value : ℝ) : Tma.DescriptorAgreement (candidate value).view (dataMaps 3) := by
  intro id op he
  cases id with
  | mk issue =>
    have hh := Unified.view_tma_iff.mp (Tma.copyAt_iff.mp he)
    have hc := retry_candidate_resource_case (family value) (by decide) (source_well_formed value (fun _ => .bits (byte 0))) issue (.base (.tmaIssue op)) hh rfl
    cases hc with
    | copyA tile ht => interval_cases tile <;> rfl
    | copyB tile ht => interval_cases tile <;> rfl

theorem all_resource_histories_admitted (value : ℝ) (loc : Location) :
    Tma.HistoryValid Tma.localShared (candidate value).view loc (retryHistories (family value) loc) :=
  retry_all_histories_valid (family value) (by decide) (source_well_formed value (fun _ => .bits (byte 0))) (actual_descriptor_admission value) loc

theorem actual_inventory_permutation (value : ℝ) (slot : Stage) :
    (retryResourceHistory (family value) slot).Perm (Tma.inventory Tma.localShared (candidate value).view (dataGate slot)) :=
  retry_history_exhaustive (family value) (by decide) (source_well_formed value (fun _ => .bits (byte 0))) (actual_descriptor_admission value) slot

theorem actual_origins_unique (value : ℝ) (slot : Stage) :
    ((retryResourceHistory (family value) slot).map Tma.Entry.origin).Nodup :=
  retry_history_origins_unique (family value) (source_well_formed value (fun _ => .bits (byte 0))) (actual_descriptor_admission value) slot

theorem actual_source_order (value : ℝ) (slot : Stage) : Tma.SourceOrder (retryResourceHistory (family value) slot) :=
  retry_history_source_order (family value) (source_well_formed value (fun _ => .bits (byte 0))) (actual_descriptor_admission value) slot

theorem all_a_completions_observed (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) :
    Access.CompletionObserved Tma.localShared (candidate value).view (retryHistories (family value)) dataCluster
      ((family value).copyAId tile) ((family value).waitId tile lane) :=
  retry_a_completion_observed (family value) (by decide) (source_well_formed value (fun _ => .bits (byte 0))) (actual_descriptor_admission value) tile tile.isLt lane

theorem all_b_completions_observed (value : ℝ) (tile : Fin 3) (lane : Wgmma.Lane) :
    Access.CompletionObserved Tma.localShared (candidate value).view (retryHistories (family value)) dataCluster
      ((family value).copyBId tile) ((family value).waitId tile lane) :=
  retry_b_completion_observed (family value) (by decide) (source_well_formed value (fun _ => .bits (byte 0))) (actual_descriptor_admission value) tile tile.isLt lane

theorem erasing_actual_failed_waits_rejected (value : ℝ) :
    ¬Tma.HistoryValid Tma.localShared (candidate value).view (dataGate 0)
      (Tma.RetryErasure.erase (retryResourceHistory (family value) 0)) := by
  intro hv
  have he := family_failed_wait_at (family value) (source_well_formed value (fun _ => .bits (byte 0))) 0 (by decide) 0 0 (by change 0 < 1; decide)
  have hr : Tma.resourceAt Tma.localShared (candidate value).view (.source ((family value).failedWaitId 0 0 0)) =
      some ⟨dataGate 0,.tryWaitParity 0 false⟩ := Hopper.barrierAt_iff.mpr (Unified.view_barrier_iff.mpr he)
  have hm := Tma.history_complete hv hr
  change (⟨.source ((family value).failedWaitId 0 0 0),.tryWaitParity 0 false⟩ : Tma.Entry) ∈
    (retryResourceHistory (family value) 0).filter Tma.RetryErasure.keep at hm
  have hk := (List.mem_filter.mp hm).2
  cases hk

theorem duplicate_initialization_rejected (value : ℝ) :
    ¬Tma.HistoryValid Tma.localShared (candidate value).view (dataGate 0)
      [⟨.source ((family value).initId 0),.init 1⟩,⟨.source ((family value).initId 0),.init 1⟩] := by
  intro hv
  have hu := hv.unique
  simp at hu

theorem reversed_source_order_rejected (value : ℝ) :
    ¬Tma.SourceForward ⟨.source ((family value).invalId 0),.inval⟩ ⟨.source ((family value).initId 0),.init 1⟩ := by
  intro hf
  have hi := hf (by rfl)
  change replyTileStart 3 0 (replies value 0) (schedule 0) 3+6+0 < 0 at hi
  omega

theorem reversed_history_order_rejected (value : ℝ) :
    ¬Tma.SourceOrder [⟨.source ((family value).invalId 0),.inval⟩,⟨.source ((family value).initId 0),.init 1⟩] := by
  intro ho
  have hb : Tma.SourceBefore (.source ((family value).initId 0)) (.source ((family value).invalId 0)) := by
    refine ⟨rfl,?_⟩
    change 0 < replyTileStart 3 0 (replies value 0) (schedule 0) 3+6+0
    omega
  have hs := ho ⟨.source ((family value).initId 0),.init 1⟩ (by simp)
    ⟨.source ((family value).invalId 0),.inval⟩ (by simp) hb
  have hne : Tma.Origin.source ((family value).initId 0) ≠ .source ((family value).invalId 0) := by
    intro he
    have hx := congrArg Ptx.Event.EventId.serial (Tma.Origin.source.inj he)
    change 0 = replyTileStart 3 0 (replies value 0) (schedule 0) 3+6+0 at hx
    omega
  simpa [hne,Ne.symm hne] using hs

end
end Ptx.HopperRetryAdmissionTests
