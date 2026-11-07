import Ptx.Kernels.AmpereTiledEvents
import Ptx.Tests.AmpereTiledSource

/-! Arbitrary-fuel rejection of late bad replies, including stale packed state.
Canonical counters/old-C tests remain local source evidence, not legal memory. -/
namespace Ptx.AmpereTiledReconstructionTests
open Ptx.ISA Ptx.Ampere
noncomputable section
abbrev input := AmpereTiledSourceTests.cfg
abbrev context := AmpereTiledSourceTests.ctx input AmpereTiledSourceTests.id
abbrev good := AmpereTiledSourceTests.oracle
abbrev replies := AmpereTiledSourceTests.replies

def shortThirdCopy : Oracle := {good with bytes := fun q => if q = 22 then List.replicate 7 (.bits (byte 0)) else good.bytes q}
def integerSecondB : Oracle := {good with word32 := fun q => if q = 18 then .integer 99 else good.word32 q}
def integerThirdA : Oracle := {good with word32 := fun q => if q = 24 then .integer 99 else good.word32 q}
def matrixSlotInteger : Oracle := {good with word32 := fun q => if q%10 = 9 then .integer 99 else good.word32 q}

def matrixSlotReplies : AmpereTiledTrace.ReplySet input context matrixSlotInteger := {
  payload := fun step i => matrixSlotInteger.bytes (10*step+i.val)
  a := fun _ _ => ⟨1,1⟩
  b := fun _ _ => ⟨1,1⟩
  size := by intro step _ i; simp [matrixSlotInteger,AmpereTiledSourceTests.oracle]
  bytes := by intro step _ i; simp [AmpereTiledEntry.loopConfig]
  wordA := by
    intro step _ i
    have hi := i.isLt
    have hn : (10*step+3+i.val)%10 ≠ 9 := by omega
    simp [matrixSlotInteger,AmpereTiledEntry.loopConfig,hn,AmpereTiledSourceTests.oracle]
  wordB := by
    intro step _ i
    have hi := i.isLt
    have hn : (10*step+7+i.val)%10 ≠ 9 := by omega
    simp [matrixSlotInteger,AmpereTiledEntry.loopConfig,hn,AmpereTiledSourceTests.oracle]
}

theorem matrix_slot_word_unused : matrixSlotInteger.word32 9 = .integer 99 := rfl
theorem matrix_slot_integer_complete : Ampere.run context matrixSlotInteger AmpereTiledTrace.code 127 {} =
    .ok (AmpereTiledTrace.finalState input context matrixSlotInteger matrixSlotReplies,
      AmpereTiledTrace.events input context matrixSlotInteger matrixSlotReplies) :=
  AmpereTiledTrace.translated_run AmpereTiledSourceTests.layout context matrixSlotInteger matrixSlotReplies
    (AmpereTiledInit.canonical_params input) AmpereTiledSourceTests.valid (by constructor <;> decide)

theorem late_copy_size_rejected {count last emitted}
    (hr : Ampere.run context shortThirdCopy AmpereTiledTrace.code count {} = .ok (last,emitted)) :
    last.scalar.core.thread.status ≠ .done := by
  intro hd
  obtain ⟨r⟩ := AmpereTiledReconstruct.complete_replies AmpereTiledSourceTests.layout context shortThirdCopy
    (AmpereTiledInit.canonical_params input) AmpereTiledSourceTests.valid (by constructor <;> decide) hr hd
  have hh := r.size 2 (by change (2 : Nat) < 3; decide) (2 : Fin 3)
  have hv := r.bytes 2 (by change (2 : Nat) < 3; decide) (2 : Fin 3)
  rw [← hv] at hh
  change (7 : Nat) = 8 at hh
  omega

theorem late_b_integer_rejected {count last emitted}
    (hr : Ampere.run context integerSecondB AmpereTiledTrace.code count {} = .ok (last,emitted)) :
    last.scalar.core.thread.status ≠ .done := by
  intro hd
  obtain ⟨r⟩ := AmpereTiledReconstruct.complete_replies AmpereTiledSourceTests.layout context integerSecondB
    (AmpereTiledInit.canonical_params input) AmpereTiledSourceTests.valid (by constructor <;> decide) hr hd
  have hh := r.wordB 1 (by change (1 : Nat) < 3; decide) (1 : Fin 2)
  change Word32.integer 99 = Word32.packed (r.b 1 1) at hh
  cases hh

theorem late_a_integer_rejected {count last emitted}
    (hr : Ampere.run context integerThirdA AmpereTiledTrace.code count {} = .ok (last,emitted)) :
    last.scalar.core.thread.status ≠ .done := by
  intro hd
  obtain ⟨r⟩ := AmpereTiledReconstruct.complete_replies AmpereTiledSourceTests.layout context integerThirdA
    (AmpereTiledInit.canonical_params input) AmpereTiledSourceTests.valid (by constructor <;> decide) hr hd
  have hh := r.wordA 2 (by change (2 : Nat) < 3; decide) (1 : Fin 4)
  change Word32.integer 99 = Word32.packed (r.a 2 1) at hh
  cases hh

def old : State := {packed := [("%rb1",⟨9,9⟩)]}
def badA (_ : Fin 4) : Word32 := .packed ⟨1,1⟩
def badB (i : Fin 2) : Word32 := if i.val = 1 then .integer 99 else .packed ⟨1,1⟩
theorem old_pair_present : declarationLookup "%rb1" old.packed = some (PackedF16.mk 9 9) := rfl
theorem old_pair_invalidated : declarationLookup "%rb1" (RawLoads.loaded old badA badB).packed = none := by
  simpa [MmaBlock.bRegisters,Registers2.get,badB,Word32.packedValue] using RawLoads.loaded_b old badA badB (1 : Fin 2)

theorem automatic_counts {count last emitted}
    (hr : Ampere.run context good AmpereTiledTrace.code count {} = .ok (last,emitted))
    (hd : last.scalar.core.thread.status = .done) : count = 127 ∧ emitted.length = 55 ∧ last.scalar.core.queries = 30 :=
  AmpereTiledReconstruct.complete_counts AmpereTiledSourceTests.layout context good
    (AmpereTiledInit.canonical_params input) AmpereTiledSourceTests.valid (by constructor <;> decide) hr hd

theorem canonical_run : Ampere.run context good AmpereTiledTrace.code 127 {} =
    .ok (AmpereTiledTrace.finalState input context good replies,AmpereTiledTrace.events input context good replies) :=
  AmpereTiledTrace.translated_run AmpereTiledSourceTests.layout context good replies
    (AmpereTiledInit.canonical_params input) AmpereTiledSourceTests.valid (by constructor <;> decide)
theorem canonical_copies : (AmpereTiledTrace.finalState input context good replies).copies.length = 9 :=
  (AmpereTiledTrace.final_metadata input context good replies).1
theorem canonical_groups : (AmpereTiledTrace.finalState input context good replies).groups = 3 :=
  (AmpereTiledTrace.final_metadata input context good replies).2.1
theorem canonical_mma_calls : (AmpereTiledTrace.finalState input context good replies).mmaCalls = 3 :=
  (AmpereTiledTrace.final_metadata input context good replies).2.2.1
theorem canonical_generations : Ptx.Event.generation (AmpereTiledTrace.finalState input context good replies).scalar.core 0 = 6 :=
  (AmpereTiledTrace.final_metadata input context good replies).2.2.2.1
theorem canonical_events : (AmpereTiledTrace.events input context good replies).length = 55 :=
  AmpereTiledEvents.events_length input context good replies
theorem second_call_old_c : (AmpereTiledEvents.callAt input context good replies 1).inputs.c 0 = 42 := by
  rw [AmpereTiledEvents.call_old_c]
  rfl
theorem second_call_source_pc : (AmpereTiledEvents.callAt input context good replies 1).pc = 71 :=
  AmpereTiledEvents.call_pc _ _ _ _ _
theorem second_call_source_ordinal : (AmpereTiledEvents.callAt input context good replies 1).ordinal = 1 :=
  AmpereTiledEvents.call_ordinal _ _ _ _ _

theorem second_mma_return_event : (AmpereTiledTrace.events input context good replies)[31]? =
    some (.mmaReturn (AmpereTiledEvents.callAt input context good replies 1)) := by
  rw [show 31 = 17*1+14 by decide,AmpereTiledEvents.phase_event _ _ _ _ 1 14 (by decide) (by decide),
    AmpereTiledEvents.phase_events]
  rfl
theorem last_reuse_return_event : (AmpereTiledTrace.events input context good replies)[50]? =
    some (.ordinary (.barrierReturn 0 5)) := by
  rw [show 50 = 17*2+16 by decide,AmpereTiledEvents.phase_event _ _ _ _ 2 16 (by decide) (by decide),
    AmpereTiledEvents.phase_events]
  rfl

end
end Ptx.AmpereTiledReconstructionTests
