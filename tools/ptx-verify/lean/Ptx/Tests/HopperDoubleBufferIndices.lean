import Ptx.Kernels.HopperDoubleBufferTmaInputs
import Ptx.Tests.HopperDoubleBufferData

/-! Decidable metadata projections of the actual rich source candidate.
No equality decision procedure on reals or real-valued states is installed. -/
namespace Ptx.HopperDoubleBufferIndexTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

abbrev a := HopperDoubleBufferDataTests.a
abbrev b := HopperDoubleBufferDataTests.b

structure MmaMetadata where
  pc : Nat
  sequence : Nat
  ordinal : Nat
  group : Nat
  query : Nat
  a : Nat
  b : Nat
  deriving DecidableEq

def mmaAt (tiles : Nat) (lane : Wgmma.Lane) (index : Nat) : Option MmaMetadata :=
  ((dataCompleteCandidate a b tiles).eventAt ⟨(ctx tiles lane).id,index⟩).bind fun event =>
    match event with
    | .mma mark call => some ⟨mark.pc,mark.sequence,call.ordinal,call.group,call.query,call.a,call.b⟩
    | _ => none

structure CopyMetadata where
  base : Nat
  destination : Nat
  barrier : Nat
  query : Nat
  y : Int
  bytes : Nat
  deriving DecidableEq

def copyAt (tiles index : Nat) : Option CopyMetadata :=
  ((dataCompleteCandidate a b tiles).eventAt ⟨(ctx tiles 0).id,index⟩).bind fun event =>
    match event with
    | .base (.tmaIssue copy) => some ⟨copy.descriptor.base,copy.destination,copy.barrier,copy.queryBase,copy.coordinates.y,copy.payload.length⟩
    | _ => none

def waitAt (tiles : Nat) (lane : Wgmma.Lane) (index : Nat) : Option (Nat × Nat × Bool) :=
  ((dataCompleteCandidate a b tiles).eventAt ⟨(ctx tiles lane).id,index⟩).bind fun event =>
    match event with
    | .base (.barrier event) =>
      match event.operation with
      | .tryWaitParity parity ready => some (event.location.address,parity,ready)
      | _ => none
    | _ => none

theorem producer_mma_indices :
    [dataMmaIndex a b 3 0 0,dataMmaIndex a b 3 1 0,dataMmaIndex a b 3 2 0] = [13,23,30] := by decide
theorem peer_mma_indices :
    [dataMmaIndex a b 3 0 127,dataMmaIndex a b 3 1 127,dataMmaIndex a b 3 2 127] = [4,11,18] := by decide
theorem producer_first_mma : mmaAt 3 0 13 = some ⟨77,1,0,0,9,68720001025,68720001153⟩ := by decide
theorem producer_second_mma : mmaAt 3 0 23 = some ⟨77,5,1,1,16,68720001169,68720001297⟩ := by decide
theorem producer_final_mma : mmaAt 3 0 30 = some ⟨77,9,2,2,19,68720001025,68720001153⟩ := by decide
theorem peer_final_mma : mmaAt 3 127 18 = some ⟨77,9,2,2,7,68720001025,68720001153⟩ := by decide
theorem final_mma_has_no_prefetch_gap : mmaAt 3 0 33 = none := by decide
theorem initial_a_copy : copyAt 3 6 = some ⟨65536,16,0,0,0,2048⟩ := by decide
theorem initial_b_copy : copyAt 3 7 = some ⟨71680,2064,0,2,0,256⟩ := by decide
theorem second_a_copy : copyAt 3 10 = some ⟨65536,2320,8,5,8,2048⟩ := by decide
theorem second_b_copy : copyAt 3 11 = some ⟨71680,4368,8,7,1,256⟩ := by decide
theorem reused_a_copy : copyAt 3 20 = some ⟨65536,16,0,12,16,2048⟩ := by decide
theorem reused_b_copy : copyAt 3 21 = some ⟨71680,2064,0,14,2,256⟩ := by decide
theorem twice_reused_a_copy : copyAt 5 40 = some ⟨65536,16,0,26,32,2048⟩ := by decide
theorem twice_reused_b_copy : copyAt 5 41 = some ⟨75776,2064,0,28,4,256⟩ := by decide
theorem producer_reused_wait : waitAt 3 0 28 = some (0,1,true) := by decide
theorem peer_reused_wait : waitAt 3 127 16 = some (0,1,true) := by decide
theorem producer_second_wait : waitAt 3 0 18 = some (8,0,true) := by decide
theorem zero_tile_has_no_copy : copyAt 0 6 = none := by decide
theorem zero_tile_has_no_mma : mmaAt 0 0 6 = none := by decide
theorem final_tile_copy_ids :
    (dataCopyAId a b 3 2).issue.serial = 20 ∧ (dataCopyBId a b 3 2).issue.serial = 21 ∧
      (dataExpectId a b 3 2).serial = 19 := by decide
theorem same_slot_distinct_copy_ids : dataCopyAId a b 3 0 ≠ dataCopyAId a b 3 2 := by decide
theorem native_sequence_keeps_history :
    (dataIterationMark a b 3 2 127).sequence = 9 := by decide

end
end Ptx.HopperDoubleBufferIndexTests
