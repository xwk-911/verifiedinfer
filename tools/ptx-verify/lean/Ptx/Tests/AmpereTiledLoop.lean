import Ptx.Kernels.AmpereTiledLoop
import Ptx.Tests.AmpereTiledStage

/-! Parameterized local runs with arbitrary iteration counts and nonzero prior
history. These entries deliberately are not PC-zero or legal-memory witnesses.
The oracle's integer copy bytes and packed real words are not value-coherent. -/
namespace Ptx.AmpereTiledLoopTests
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledLoop
noncomputable section

def ctx := AmpereTiledStageTests.ctx
def cfg (tiles : Nat) : Config := ⟨⟨64,320,1024,0,256,512⟩,0,512,4096,4352,tiles,11⟩
def oracle : Oracle := {
  scalar := fun _ => .integer 0
  bytes := fun q => List.replicate 8 (.bits (byte q))
  word32 := fun _ => .packed ⟨1,1⟩
  matrix := fun q i => 100+(q : ℝ)+(i.val : ℝ)
}
def entry (tiles : Nat) : State := {
  scalar := {
    core := {thread := {pc := 57,regs := [("%it",0),("%k",16*tiles),
      ("%a",64),("%ah",320),("%b",1024),("%sa",0),("%sah",256),("%sb",512),
      ("%la",0),("%lb",512),("%c",4096),("%ch",4352)]},queries := 11,generations := [(0,8)]}
    floats := AmpereTiledStageTests.entry.scalar.floats
  }
  copies := [AmpereTiledStageTests.prior]
  groups := 4
  mmaCalls := 2
}
def replies (tiles : Nat) : Replies (cfg tiles) oracle := {
  payload := fun step i => oracle.bytes (11+10*step+i.val)
  a := fun _ _ => ⟨1,1⟩
  b := fun _ _ => ⟨1,1⟩
  size := by intro step _ i; simp [oracle]
  bytes := by intro step _ i; rfl
  wordA := by intro step _ i; rfl
  wordB := by intro step _ i; rfl
}

theorem entry_invariant (tiles : Nat) : Invariant (cfg tiles) 0 (entry tiles) := by
  constructor
  · rfl
  · rfl
  · rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · rfl
  · exact ⟨AmpereTiledStageTests.acc,by intro i; fin_cases i <;> rfl⟩
  · intro i; fin_cases i <;> rfl

theorem arbitrary_iteration_count (tiles : Nat) (hbound : 16*tiles < 2^32) :
    ∃ last emitted, Ampere.run ctx oracle code (21*tiles+7) (entry tiles) = .ok (last,emitted) ∧
      last.scalar.core.thread.status = .done ∧ emitted.length = 17*tiles+4 ∧
      last.scalar.core.queries = 11+10*tiles := by
  exact run_to_completion ctx oracle (replies tiles) hbound tiles (by simp [cfg]) (entry_invariant tiles)

theorem zero_iterations :
    ∃ last emitted, Ampere.run ctx oracle code 7 (entry 0) = .ok (last,emitted) ∧
      last.scalar.core.thread.status = .done ∧ emitted.length = 4 ∧ last.scalar.core.queries = 11 :=
  arbitrary_iteration_count 0 (by decide)

theorem three_iterations :
    ∃ last emitted, Ampere.run ctx oracle code 70 (entry 3) = .ok (last,emitted) ∧
      last.scalar.core.thread.status = .done ∧ emitted.length = 55 ∧ last.scalar.core.queries = 41 :=
  arbitrary_iteration_count 3 (by decide)

theorem incorrect_completed_count_rejected {last emitted}
    (hrun : Ampere.run ctx oracle code 69 (entry 3) = .ok (last,emitted)) :
    last.scalar.core.thread.status ≠ .done := by
  intro hd
  have hc := complete_run_counts ctx oracle (replies 3) (by decide) 3 rfl (entry_invariant 3) hrun hd
  have hh : (69 : Nat) = 70 := hc.1
  omega

theorem copy_reply_is_not_mma_word :
    oracle.bytes 14 ≠ Word32.encode (oracle.word32 14) := by
  intro he
  have hl := congrArg List.length he
  change (8 : Nat) = 4 at hl
  omega

end
end Ptx.AmpereTiledLoopTests
