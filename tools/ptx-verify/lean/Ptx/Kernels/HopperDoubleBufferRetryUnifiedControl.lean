import Ptx.Kernels.HopperDoubleBufferRetryNativeRanks

/-! Full unified source/TMA/resource/CTA/native construct-control admission
for arbitrary finite retry families on the positive-K path. This proves
structural control only, not memory/tensor or physical-runtime admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_base_control_order {tiles initial candidate left right} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (he : Tma.ControlEdge candidate.view (retryHistories family) left right) :
    retryUnifiedRank family (.base left) < retryUnifiedRank family (.base right) := by
  apply Nat.mul_lt_mul_of_pos_left _ (by decide)
  rcases he with hp | hc | hi | hr
  · exact retry_tma_program_order family hb hp
  · exact retry_control_cta_order family hb hc
  · exact retry_tma_internal_order family ht hb hi
  · exact retry_control_resource_order family hr

theorem retry_unified_edge_order {tiles initial candidate left right} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (he : Unified.ControlEdge HopperStage.block candidate (retryHistories family) left right) :
    retryUnifiedRank family left < retryUnifiedRank family right := by
  rcases he with he | ha | hr | hi | hf
  · cases left <;> cases right <;> try exact False.elim he
    exact retry_base_control_order family ht hw he
  · exact retry_native_arrival_order family hw ha
  · exact retry_native_rendezvous_order family hw hr
  · exact retry_native_issue_order family hw hi
  · exact retry_native_finish_order family hw hb hf

theorem retry_unified_control_acyclic {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) :
    Unified.ControlAcyclic HopperStage.block candidate (retryHistories family) :=
  Unified.control_acyclic_of_rank (retryUnifiedRank family) (fun _ _ => retry_unified_edge_order family ht hb hw)

theorem retry_control_admitted {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) :
    Unified.ControlAdmitted HopperStage.block candidate (retryHistories family) :=
  ⟨retry_native_schedules_admitted family hw,retry_unified_control_acyclic family ht hb hw⟩

theorem completed_positive_control_admitted {tiles initial candidate} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate) :
    ∃ family : ReplySourceFamily tiles candidate, Unified.ControlAdmitted HopperStage.block candidate (retryHistories family) := by
  obtain ⟨family⟩ := completed_candidate_reply_family ht hb hw hc
  exact ⟨family,retry_control_admitted family ht hb hw⟩

end
end Ptx.Kernels.HopperDoubleBuffer
