import Ptx.Kernels.HopperDoubleBufferRetryResourceOrder
import Ptx.Kernels.HopperDoubleBufferNativePublication

/-! Actual exhaustive, unique, source-ordered retry histories and admitted
completion observations. Combined control/native memory/tensor/observer and
fully admitted launch correctness are not inferred from resource admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_stage_history_valid {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (slot) :
    Tma.HistoryValid Tma.localShared candidate.view (dataGate slot) (retryResourceHistory family slot) :=
  ⟨retry_history_origins_unique family hw hd slot,retry_history_exhaustive family ht hw hd slot,
    retry_history_source_order family hw hd slot,⟨none,retry_history_protocol family slot⟩⟩

def retryHistories {tiles candidate} (family : ReplySourceFamily tiles candidate) (loc : Location) : List Tma.Entry :=
  if loc = dataGate 0 then retryResourceHistory family 0 else
    if loc = dataGate 1 then retryResourceHistory family 1 else []

theorem retry_histories_at_gate {tiles candidate} (family : ReplySourceFamily tiles candidate) (slot : Stage) :
    retryHistories family (dataGate slot) = retryResourceHistory family slot := by fin_cases slot <;> rfl

theorem retry_all_histories_valid {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (loc : Location) :
    Tma.HistoryValid Tma.localShared candidate.view loc (retryHistories family loc) := by
  by_cases hz : loc = dataGate 0
  · subst loc
    rw [retry_histories_at_gate]
    exact retry_stage_history_valid family ht hw hd 0
  · by_cases ho : loc = dataGate 1
    · subst loc
      rw [retry_histories_at_gate]
      exact retry_stage_history_valid family ht hw hd 1
    · have hout : ∀ slot, loc ≠ dataGate slot := by intro slot; fin_cases slot <;> assumption
      have hi := retry_inventory_outside_gates family ht hw hd loc hout
      simp only [retryHistories,hz,ho,ite_false]
      refine ⟨List.nodup_nil,?_,?_,⟨none,rfl⟩⟩
      · rw [hi]
      · simp [Tma.SourceOrder]

theorem retry_a_completion_observed {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (hp : tile < tiles) (lane : Wgmma.Lane) :
    Access.CompletionObserved Tma.localShared candidate.view (retryHistories family) dataCluster (family.copyAId tile) (family.waitId tile lane) := by
  refine ⟨?_,dataGate (stage tile),retryNoticeAIndex family (stage tile) (tile/2),retryPhaseWaitIndex family (stage tile) (tile/2) lane,
    rfl,retry_all_histories_valid family ht hw hd _,?_⟩
  · cases tile <;> rfl
  · rw [retry_histories_at_gate]
    simpa only [stage_tile_index] using retry_observe_a family (stage tile) (tile/2) (tile_phase_in_range tiles tile hp) lane

theorem retry_b_completion_observed {tiles initial candidate} (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (tile : Nat) (hp : tile < tiles) (lane : Wgmma.Lane) :
    Access.CompletionObserved Tma.localShared candidate.view (retryHistories family) dataCluster (family.copyBId tile) (family.waitId tile lane) := by
  refine ⟨?_,dataGate (stage tile),retryNoticeBIndex family (stage tile) (tile/2),retryPhaseWaitIndex family (stage tile) (tile/2) lane,
    rfl,retry_all_histories_valid family ht hw hd _,?_⟩
  · cases tile <;> rfl
  · rw [retry_histories_at_gate]
    simpa only [stage_tile_index] using retry_observe_b family (stage tile) (tile/2) (tile_phase_in_range tiles tile hp) lane

theorem completed_candidate_admitted_retry_histories {tiles initial candidate} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) :
    ∃ family : ReplySourceFamily tiles candidate,
      (∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (retryHistories family loc)) ∧
      (∀ tile, tile < tiles → ∀ lane,
        Access.CompletionObserved Tma.localShared candidate.view (retryHistories family) dataCluster (family.copyAId tile) (family.waitId tile lane) ∧
        Access.CompletionObserved Tma.localShared candidate.view (retryHistories family) dataCluster (family.copyBId tile) (family.waitId tile lane)) := by
  obtain ⟨family⟩ := completed_candidate_reply_family ht hb hw hc
  exact ⟨family,retry_all_histories_valid family ht hw hd,
    fun tile hp lane => ⟨retry_a_completion_observed family ht hw hd tile hp lane,retry_b_completion_observed family ht hw hd tile hp lane⟩⟩

end
end Ptx.Kernels.HopperDoubleBuffer
