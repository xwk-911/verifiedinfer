import Ptx.Kernels.HopperDoubleBufferControlAdmission
import Ptx.Hopper.UnifiedVisibility

/-! Each actual tile's TMA writes publish to its 128-lane WGMMA operand
reads through source-matched completion observations and source program
order. These byte edges do not establish RF/co, reuse protection, native
control admission, eligibility, or a complete memory/launch witness. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

/-- The source launch has one CTA; no cross-CTA scope is assumed. -/
def dataCluster : Access.ClusterScope := fun left right => left.cta = right.cta

theorem data_a_completion_observed (a b tiles tile lane) (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    Access.CompletionObserved Tma.localShared (dataCompleteCandidate a b tiles).view
      (dataHistories a b tiles) dataCluster (dataCopyAId a b tiles tile) (dataWaitId a b tiles tile lane) := by
  refine ⟨rfl,dataGate (stage tile),noticeAIndex (tile/2),phaseWaitIndex (tile/2) lane,rfl,
    data_all_histories_valid a b tiles hb _,?_⟩
  rw [data_histories_at_gate]
  simpa only [stage_tile_index] using
    data_observe_a a b tiles (stage tile) (tile/2) (tile_phase_in_range tiles tile ht) lane

theorem data_b_completion_observed (a b tiles tile lane) (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    Access.CompletionObserved Tma.localShared (dataCompleteCandidate a b tiles).view
      (dataHistories a b tiles) dataCluster (dataCopyBId a b tiles tile) (dataWaitId a b tiles tile lane) := by
  refine ⟨rfl,dataGate (stage tile),noticeBIndex (tile/2),phaseWaitIndex (tile/2) lane,rfl,
    data_all_histories_valid a b tiles hb _,?_⟩
  rw [data_histories_at_gate]
  simpa only [stage_tile_index] using
    data_observe_b a b tiles (stage tile) (tile/2) (tile_phase_in_range tiles tile ht) lane

theorem data_wait_program_before_mma (a b tiles tile lane) (ht : tile < tiles) :
    Hopper.ProgramOrder (dataCompleteCandidate a b tiles).view
      (dataWaitId a b tiles tile lane) (dataMmaId a b tiles tile lane) := by
  refine ⟨?_,?_,rfl,?_⟩
  · apply (Unified.view_present_iff _ _).mpr
    change ((dataCompleteCandidate a b tiles).eventAt (dataWaitId a b tiles tile lane)).isSome = true
    rw [show (dataCompleteCandidate a b tiles).eventAt (dataWaitId a b tiles tile lane) = _ from
      data_candidate_wait_at a b tiles tile lane ht]
    rfl
  · apply (Unified.view_present_iff _ _).mpr
    change ((dataCompleteCandidate a b tiles).eventAt (dataMmaId a b tiles tile lane)).isSome = true
    rw [data_candidate_mma_at a b tiles tile lane ht]
    rfl
  · dsimp only [dataWaitId,dataMmaId,dataMmaIndex]
    omega

theorem data_wait_before_mma (a b tiles tile lane) (ht : tile < tiles) :
    Access.GenericAfter (dataCompleteCandidate a b tiles).view
      (dataWaitId a b tiles tile lane) (dataMmaId a b tiles tile lane) :=
  Access.generic_program_after (data_wait_program_before_mma a b tiles tile lane ht)

theorem data_a_native_ready (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (p : Wgmma.ACoord) (byte : Fin 2) :
    Unified.TmaReady Tma.localShared (dataCompleteCandidate a b tiles) (dataHistories a b tiles) dataCluster
      (dataCopyAId a b tiles tile) (Wgmma.aOffset (p,byte)).val (dataMmaId a b tiles tile 0) (.a p byte)
      (Wgmma.operandLocation .zero (dataIterationCall a b tiles tile 0) (.a p byte)) :=
  ⟨dataCollective a b tiles tile ht,(data_operand_a_transfer a b tiles tile 0 ht hb p byte).1,rfl,
    fun lane => ⟨dataWaitId a b tiles tile lane,data_a_completion_observed a b tiles tile lane ht hb,
      data_wait_before_mma a b tiles tile lane ht⟩⟩

theorem data_b_native_ready (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (p : Wgmma.BCoord) (byte : Fin 2) :
    Unified.TmaReady Tma.localShared (dataCompleteCandidate a b tiles) (dataHistories a b tiles) dataCluster
      (dataCopyBId a b tiles tile) (Wgmma.bOffset (p,byte)).val (dataMmaId a b tiles tile 0) (.b p byte)
      (Wgmma.operandLocation .zero (dataIterationCall a b tiles tile 0) (.b p byte)) :=
  ⟨dataCollective a b tiles tile ht,(data_operand_b_transfer a b tiles tile 0 ht hb p byte).1,rfl,
    fun lane => ⟨dataWaitId a b tiles tile lane,data_b_completion_observed a b tiles tile lane ht hb,
      data_wait_before_mma a b tiles tile lane ht⟩⟩

def dataNativeRead (a : TileA) (b : TileB) (tiles tile : Nat) (operand : Wgmma.OperandByte) : Unified.Node :=
  .wgmmaRead (dataMmaId a b tiles tile 0) operand
def dataNativeProducer (a : TileA) (b : TileB) (tiles tile : Nat) : Wgmma.OperandByte → Unified.Node
  | .a p byte => .base (.tma (.write (dataCopyAId a b tiles tile) (Wgmma.aOffset (p,byte)).val))
  | .b p byte => .base (.tma (.write (dataCopyBId a b tiles tile) (Wgmma.bOffset (p,byte)).val))
def dataNativeLocation (a : TileA) (b : TileB) (tiles tile : Nat) (operand : Wgmma.OperandByte) : Location :=
  Wgmma.operandLocation .zero (dataIterationCall a b tiles tile 0) operand

theorem data_native_publication (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (operand : Wgmma.OperandByte) :
    Unified.NativePublished Tma.localShared (dataCompleteCandidate a b tiles) (dataHistories a b tiles) dataCluster
      (dataNativeLocation a b tiles tile operand) (dataNativeProducer a b tiles tile operand) (dataNativeRead a b tiles tile operand) := by
  cases operand with
  | a p byte => exact data_a_native_ready a b tiles tile ht hb p byte
  | b p byte => exact data_b_native_ready a b tiles tile ht hb p byte

theorem data_native_byte_order (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster (dataNativeLocation a b tiles tile operand)
      (dataNativeProducer a b tiles tile operand) (dataNativeRead a b tiles tile operand) :=
  Unified.native_published_byte_order (data_native_publication a b tiles tile ht hb operand)

end
end Ptx.Kernels.HopperDoubleBuffer
