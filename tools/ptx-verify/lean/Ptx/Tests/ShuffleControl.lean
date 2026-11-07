import Ptx.Tests.Shuffle

/-! A graph regression for two incompatible groups attempting to exempt each
other as exited. This is a graph counterexample, not a claimed source program. -/
namespace Ptx.ShuffleControlTests
open Ptx.ISA Ptx.Shuffle
open Ptx.Kernels.ShufflePair
noncomputable section

def leftRecord : Record := ⟨⟨.up,3⟩,0,1,0,0,0,0,true⟩
def rightRecord : Record := ⟨⟨.idx,3⟩,0,4,1,1,31,1,true⟩
def leftTrace : Shuffle.ThreadTrace :=
  ⟨id 0,oracle 0 true,0,{base := {core := {thread := {status := .done}}},visits := [(leftRecord.key,1)]},[.shuffle leftRecord]⟩
def rightTrace : Shuffle.ThreadTrace :=
  ⟨id 1,oracle 1 true,0,{base := {core := {thread := {status := .done}}},visits := [(rightRecord.key,1)]},[.shuffle rightRecord]⟩
def mutuallyExempt : Shuffle.Candidate := ⟨[leftTrace,rightTrace]⟩

theorem incompatible_groups_have_no_source_match :
    ¬Source block (event 0) leftRecord (event 1) rightRecord := by
  intro hs
  have hk := hs.2.2.2.1
  cases hk

theorem other_group_has_zero_generation :
    ExitedBefore leftTrace rightRecord.key 0 ∧ ExitedBefore rightTrace leftRecord.key 0 := by
  constructor <;> exact ⟨rfl,by decide⟩

theorem mutual_exit_exemptions_create_a_cycle :
    Ptx.Event.Path (ControlEdge block mutuallyExempt) (.returned (event 0)) (.returned (event 0)) := by
  have exitLeft : ControlEdge block mutuallyExempt (.returned (event 0)) (.exited (id 0)) :=
    .exit (block := block) (candidate := mutuallyExempt) (id := event 0) (event := .shuffle leftRecord)
      (trace := leftTrace) (by rfl) (by simp [mutuallyExempt]) rfl rfl
  have exemptLeft : ControlEdge block mutuallyExempt (.exited (id 0)) (.returned (event 1)) :=
    .exitedPeer (record := rightRecord) (trace := leftTrace) (by rfl) (by simp [mutuallyExempt])
      (by constructor <;> decide) (by decide) other_group_has_zero_generation.1
  have exitRight : ControlEdge block mutuallyExempt (.returned (event 1)) (.exited (id 1)) :=
    .exit (block := block) (candidate := mutuallyExempt) (id := event 1) (event := .shuffle rightRecord)
      (trace := rightTrace) (by rfl) (by simp [mutuallyExempt]) rfl rfl
  have exemptRight : ControlEdge block mutuallyExempt (.exited (id 1)) (.returned (event 0)) :=
    .exitedPeer (record := leftRecord) (trace := rightTrace) (by rfl) (by simp [mutuallyExempt])
      (by constructor <;> decide) (by decide) other_group_has_zero_generation.2
  exact .trans (.single exitLeft) (.trans (.single exemptLeft) (.trans (.single exitRight) (.single exemptRight)))

theorem mutually_exempt_groups_are_not_control_admitted : ¬ControlAdmitted block mutuallyExempt := by
  intro ha
  exact ha _ mutual_exit_exemptions_create_a_cycle

theorem different_static_pcs_can_match :
    Source block (event 0) (record 0 1 true) (event 1) {record 1 0 true with pc := 999} := by
  exact (pair_source_iff 0 1 1 0 true true).2 (by decide)

theorem different_generations_cannot_match :
    ¬Source block (event 0) (record 0 1 true) (event 1) {record 1 0 true with generation := 1} := by
  intro hs
  exact Nat.one_ne_zero hs.2.2.2.2

theorem different_masks_cannot_match :
    ¬Source block (event 0) (record 0 1 true) (event 1) {record 1 0 true with key := ⟨.bfly,7⟩} := by
  intro hs
  have hk := congrArg Key.mask hs.2.2.2.1
  norm_num [record,key] at hk

theorem different_ctas_cannot_match :
    ¬Source block (event 0) (record 0 1 true) ⟨⟨.one,⟨1,0,0⟩⟩,0⟩ (record 1 0 true) := by
  intro hs
  have hc := hs.1.1
  cases hc

theorem next_warp_cannot_supply_a_lane :
    ¬Source ⟨64,1,1⟩ (event 0) (record 0 1 true) ⟨⟨.zero,⟨33,0,0⟩⟩,0⟩ (record 1 0 true) := by
  intro hs
  have hw := hs.1.2
  norm_num [linear,Dim3.linear,event,Kernels.ShufflePair.id] at hw

end
end Ptx.ShuffleControlTests
