import Ptx.Kernels.HopperDoubleBufferNativeReuse
import Ptx.Tests.HopperDoubleBufferData

/-! Metadata-only execution checks and arbitrary-real publication/completion/
reuse proofs. These are memory components, not a complete admitted witness. -/
namespace Ptx.HopperDoubleBufferNativePublicationTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

abbrev a := HopperDoubleBufferDataTests.a
abbrev b := HopperDoubleBufferDataTests.b
def waitMeta (tiles : Nat) (lane : Wgmma.Lane) (serial : Nat) : Option (Nat × Nat × Nat × Nat × Nat × Nat) :=
  ((dataCompleteCandidate a b tiles).eventAt ⟨(ctx tiles lane).id,serial⟩).bind fun event => match event with
    | .wait mark groups keep before after query => some (mark.sequence,groups,keep,before,after,query)
    | _ => none
def producerMeta (tiles tile : Nat) (operand : Wgmma.OperandByte) : Option (Nat × Nat) :=
  match dataNativeProducer a b tiles tile operand with
  | .base (.tma (.write copy offset)) => some (copy.issue.serial,offset)
  | _ => none
def operandAddress (tiles tile : Nat) (operand : Wgmma.OperandByte) : Nat :=
  (dataNativeLocation a b tiles tile operand).address

theorem first_producer_wait : waitMeta 3 0 15 = some (3,1,0,0,1,10) := by decide
theorem middle_producer_wait : waitMeta 3 0 25 = some (7,2,0,1,2,17) := by decide
theorem final_producer_wait : waitMeta 3 0 32 = some (11,3,0,2,3,20) := by decide
theorem first_peer_wait : waitMeta 3 127 6 = some (3,1,0,0,1,2) := by decide
theorem final_peer_wait : waitMeta 3 127 20 = some (11,3,0,2,3,8) := by decide
theorem twice_reused_producer_wait : waitMeta 5 0 52 = some (19,5,0,4,5,34) := by decide
theorem twice_reused_peer_wait : waitMeta 5 127 34 = some (19,5,0,4,5,14) := by decide
theorem single_tile_wait : waitMeta 1 0 12 = some (3,1,0,0,1,6) := by decide
theorem cta_has_no_native_completion : waitMeta 3 0 33 = none ∧ waitMeta 3 127 21 = none := by decide
theorem mbarrier_has_no_native_completion : waitMeta 3 0 28 = none ∧ waitMeta 3 127 16 = none := by decide
theorem commit_has_no_native_completion : waitMeta 3 0 31 = none := by decide
theorem zero_tile_has_no_native_wait : waitMeta 0 0 9 = none := by decide
theorem first_operand_producers : producerMeta 3 0 (.a (0,0) 0) = some (6,0) ∧ producerMeta 3 0 (.b (0,0) 0) = some (7,0) := by decide
theorem reused_operand_producers : producerMeta 3 2 (.a (63,15) 1) = some (20,2047) ∧ producerMeta 3 2 (.b (15,7) 1) = some (21,255) := by decide
theorem twice_reused_operand_producers : producerMeta 5 4 (.a (0,0) 0) = some (40,0) ∧ producerMeta 5 4 (.b (0,0) 0) = some (41,0) := by decide
theorem alternate_operand_addresses : operandAddress 3 0 (.a (0,0) 0) = 16 ∧ operandAddress 3 1 (.a (0,0) 0) = 2320 := by decide
theorem reused_operand_addresses : operandAddress 3 2 (.a (63,15) 1) = 2063 ∧ operandAddress 3 2 (.b (15,7) 1) = 2319 := by decide

theorem arbitrary_real_publication (x : TileA) (y : TileB) (tiles tile : Nat)
    (ht : tile < tiles) (hb : tiles ≤ 2^28) (operand : Wgmma.OperandByte) :
    Unified.NativePublished Tma.localShared (dataCompleteCandidate x y tiles) (dataHistories x y tiles) dataCluster
      (dataNativeLocation x y tiles tile operand) (dataNativeProducer x y tiles tile operand) (dataNativeRead x y tiles tile operand) :=
  data_native_publication x y tiles tile ht hb operand

theorem arbitrary_real_completion (x : TileA) (y : TileB) (tiles tile : Nat) (lane : Wgmma.Lane)
    (ht : tile < tiles) (hb : tiles ≤ 2^28) :
    Unified.WgmmaCompletedAt (dataCompleteCandidate x y tiles) (dataMmaId x y tiles tile 0) (dataNativeWaitId x y tiles tile lane) :=
  data_native_completed x y tiles tile lane ht hb

theorem arbitrary_real_reuse (x : TileA) (y : TileB) (tiles tile next : Nat)
    (hn : next < tiles) (hle : tile+2 ≤ next) (hs : stage next = stage tile) (hb : tiles ≤ 2^28) (operand : Wgmma.OperandByte) :
    Unified.NativeReuse Tma.localShared (dataCompleteCandidate x y tiles) (dataNativeLocation x y tiles tile operand)
      (dataNativeRead x y tiles tile operand) (dataNativeProducer x y tiles next operand) :=
  data_native_reuse x y tiles tile next hn hle hs hb operand

theorem last_lane_reuse_order :
    Access.GenericAfter (dataCompleteCandidate a b 3).view (dataNativeWaitId a b 3 0 127) (dataCopyAId a b 3 2).issue :=
  data_native_wait_before_copy_a a b 3 0 2 127 (by decide) (by decide) (by decide)

theorem twice_reused_native_order (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 5)
      (dataHistories a b 5) dataCluster (dataNativeLocation a b 5 0 operand)
      (dataNativeRead a b 5 0 operand) (dataNativeProducer a b 5 4 operand) :=
  data_native_reuse_byte_order a b 5 0 4 (by decide) (by decide) (by decide) (by decide) operand

theorem cta_completion_rejected :
    ¬Unified.WgmmaCompletedAt (dataCompleteCandidate a b 3) (dataMmaId a b 3 2 0) (reuseCtaId a b 3 2 127 true) :=
  data_cta_is_not_native_completion a b 3 2 127 (by decide) true _

theorem mbarrier_completion_rejected :
    ¬Unified.WgmmaCompletedAt (dataCompleteCandidate a b 3) (dataMmaId a b 3 2 0) (dataWaitId a b 3 2 127) :=
  data_mbarrier_is_not_native_completion a b 3 2 127 (by decide) _

theorem wrapped_parity_does_not_publish_stale_a :
    Tma.observation (dataHistories a b 5 (dataGate 0)) (noticeAIndex 0) (phaseWaitIndex 2 127) = none := by
  rw [data_histories_at_gate]
  exact data_old_phase_not_observed a b 5 0 0 2 (by decide) (by decide) (by decide) 127

theorem wrapped_parity_does_not_publish_stale_b :
    Tma.observation (dataHistories a b 5 (dataGate 0)) (noticeBIndex 0) (phaseWaitIndex 2 127) = none := by
  rw [data_histories_at_gate]
  exact data_old_b_phase_not_observed a b 5 0 0 2 (by decide) (by decide) (by decide) 127

end
end Ptx.HopperDoubleBufferNativePublicationTests
