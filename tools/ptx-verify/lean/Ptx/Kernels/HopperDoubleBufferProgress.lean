import Ptx.Hopper.PrefixExecution
import Ptx.Kernels.HopperDoubleBufferRetryDataExecution

/-! Actual finite prefix execution for the existing positive-K source/control
family. Resource histories and ordering come from the original model components;
no new scheduling, completion or physical memory assumption is introduced. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section

theorem retry_family_full_prefix {tiles initial candidate}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (retryHistories family loc)) :
    Progress.Reached HopperStage.block candidate (retryHistories family) (Progress.Present candidate) :=
  Progress.full_prefix_reached hh (retryUnifiedRank family) (fun _ _ => retry_unified_edge_order family ht hb hw)

theorem retry_family_rank_prefix {tiles initial candidate}
    (family : ReplySourceFamily tiles candidate) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (retryHistories family loc)) (limit : Nat) :
    Progress.Reached HopperStage.block candidate (retryHistories family)
      (fun node => Progress.Present candidate node ∧ retryUnifiedRank family node < limit) :=
  Progress.actual_rank_prefix_reached hh (retryUnifiedRank family) (fun _ _ => retry_unified_edge_order family ht hb hw) limit

theorem retry_data_full_prefix (a b tiles schedules) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Progress.Reached HopperStage.block (retryDataCandidate a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) (Progress.Present (retryDataCandidate a b tiles schedules)) := by
  have he := retry_data_complete_components a b tiles schedules (fun _ => .bits (byte 0)) ht hb
  exact retry_family_full_prefix (retryDataFamily a b tiles schedules) ht hb he.1.source he.1.histories_valid

end
end Ptx.Kernels.HopperDoubleBuffer
