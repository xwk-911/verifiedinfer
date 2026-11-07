import Ptx.Iris.ByteContentsControl
import Ptx.Kernels.HopperDoubleBufferByteContents
import Ptx.Kernels.HopperDoubleBufferProgress

/-! Actual native arrival steps at reachable ranked source cuts. Local byte
payloads are explicit; the control-prefix witness alone does not establish that
all preceding writes have already been simulated by a value script.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def byteArrivalCut {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (lane : Wgmma.Lane) (index : Fin 4) : Cut :=
  fun node => Present candidate node ∧ retryUnifiedRank family node < retryUnifiedRank family (.arrival (family.nativeId tile lane index))

def byteArrivalState {tiles candidate} (family : ReplySourceFamily tiles candidate)
    (tile : Nat) (lane : Wgmma.Lane) (index : Fin 4) (locations : List Location) (initial : Location → Symbolic.Byte) : ByteContents.State :=
  ⟨⟨Ptx.Async.initial 0 [],byteArrivalCut family tile lane index⟩,ByteContents.initialCells locations initial⟩

theorem retry_byte_arrival_prefix {tiles sourceInitial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (retryHistories family loc))
    (tile : Nat) (lane : Wgmma.Lane) (index : Fin 4) :
    Reached HopperStage.block candidate (retryHistories family) (byteArrivalCut family tile lane index) :=
  retry_family_rank_prefix family ht hb hw hh _

theorem retry_byte_arrival_ready {tiles sourceInitial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (retryHistories family loc))
    (tile : Nat) (hit : tile < tiles) (lane : Wgmma.Lane) (index : Fin 4) :
    ByteAuthority.Ready HopperStage.block candidate (retryHistories family) (byteArrivalCut family tile lane index) (.arrival (family.nativeId tile lane index)) := by
  apply ByteAuthority.ready_at_rank_cut hh (retryUnifiedRank family) (fun _ _ => retry_unified_edge_order family ht hb hw)
  change (candidate.nativeSignatureAt (family.nativeId tile lane index)).isSome = true
  rw [retry_actual_native_signature family hw tile hit lane index]
  rfl

theorem retry_byte_arrival_finishes {tiles sourceInitial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (retryHistories family loc))
    (tile : Nat) (hit : tile < tiles) (lane : Wgmma.Lane) (index : Fin 4) (locations : List Location) (initial : Location → Symbolic.Byte) :
    ByteContents.finishControl HopperStage.block candidate (retryHistories family) (.arrival (family.nativeId tile lane index))
      (byteArrivalState family tile lane index locations initial) =
      .ok (ByteContents.controlFinished (byteArrivalState family tile lane index locations initial) (.arrival (family.nativeId tile lane index))) := by
  apply ByteContents.finish_arrival_succeeds (retry_byte_arrival_ready family ht hb hw hh tile hit lane index)
  apply ByteContents.available_control_frame
  intro k payload hg
  exact ByteContents.initialCells_owner_available hg

theorem retry_byte_arrival_script_run {tiles sourceInitial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28) (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate)
    (hh : ∀ loc, Tma.HistoryValid Tma.localShared candidate.view loc (retryHistories family loc))
    (tile : Nat) (hit : tile < tiles) (lane : Wgmma.Lane) (index : Fin 4) (locations : List Location) (initial : Location → Symbolic.Byte) :
    IrisExecution.run (ByteContentsHeap.transition (byteContentsContext family)) [.control (.arrival (family.nativeId tile lane index))]
      (byteArrivalState family tile lane index locations initial) =
      .ok (ByteContents.controlFinished (byteArrivalState family tile lane index locations initial) (.arrival (family.nativeId tile lane index))) := by
  change (ByteContents.finishControl HopperStage.block candidate (retryHistories family)
    (.arrival (family.nativeId tile lane index)) (byteArrivalState family tile lane index locations initial)).bind _ = _
  rw [retry_byte_arrival_finishes family ht hb hw hh tile hit lane index locations initial]
  rfl

end
end Ptx.Kernels.HopperDoubleBuffer
