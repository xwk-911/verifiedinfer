import Ptx.Kernels.StreamPipeline
import Mathlib.Tactic.NormNum

/-! Complete actual-kernel stream witnesses, stale-input rejection, fresh shared
state, and finite-observer publication counterexamples. This is not the MoE case.
-/
namespace Ptx.StreamTests
open Ptx.ISA Ptx.Scalar.Stream Ptx.StreamPipeline
noncomputable section

def heap (address : Nat) : Symbolic.Byte :=
  if 128 ≤ address ∧ address < 132 then .realPart .f32 2 (address-128) else .bits (byte 165)

theorem pre : Pre 2 heap := by
  intro offset ho
  change offset < 4 at ho
  have hlo : 128 ≤ 128+offset := by omega
  have hhi : 128+offset < 132 := by omega
  simp [heap,hlo,hhi]

theorem initial_a_not_initialized : ¬ Represents .f32 heap 64 9 := by
  intro h
  have hh := h 0 (by decide)
  norm_num [heap] at hh

theorem initial_c_not_initialized : ¬ Represents .f32 heap 192 18 := by
  intro h
  have hh := h 0 (by decide)
  norm_num [heap] at hh

theorem pipeline_exists : ∃ after, Runs [literal,matmul] heap after := StreamPipeline.nonvacuous 2 heap pre

theorem every_pipeline_output {after : Heap} (hr : Runs [literal,matmul] heap after) :
    Represents .f32 after 192 18 ∧ after 250 = .bits (byte 165) := by
  have h := StreamPipeline.correct 2 heap after pre hr
  norm_num [Post,heap] at h
  exact h

theorem legal_pipeline_output : ∃ after, Runs [literal,matmul] heap after ∧
    Represents .f32 after 192 18 ∧ after 250 = .bits (byte 165) := by
  obtain ⟨after,hr⟩ := pipeline_exists
  exact ⟨after,hr,every_pipeline_output hr⟩

theorem first_stage_changes_input {mid : Heap} (hr : Runs [literal] heap mid) : mid ≠ heap := by
  intro he
  have h := (StreamPipeline.literal_correct 2 heap mid pre hr).1
  rw [he] at h
  exact initial_a_not_initialized h

theorem stale_successor_initial_rejected : ¬ Runs [literal] heap heap := by
  intro h
  exact first_stage_changes_input h rfl

theorem fresh_shared (before after : Heap) :
    (literal.launch before).initial ⟨.shared .zero,0⟩ = .bits (byte 17) ∧
    (matmul.launch after).initial ⟨.shared .zero,0⟩ = .bits (byte 23) := ⟨rfl,rfl⟩

def poison : Scalar.Observation := ⟨[],fun _ => .bits (byte 0),fun _ => .initial⟩
def old : Scalar.ByteMap := fun _ => .bits (byte 165)
theorem unobserved_payload_not_published :
    Event.published old poison ⟨.global,250⟩ = .bits (byte 165) := rfl
theorem poisoned_raw_payload_differs :
    poison.output ⟨.global,250⟩ ≠ Event.published old poison ⟨.global,250⟩ := by
  change Symbolic.Byte.bits (byte 0) ≠ .bits (byte 165)
  intro h
  exact (show byte 0 ≠ byte 165 by decide) (Symbolic.Byte.bits.inj h)

theorem omitted_write_not_covered : ¬ Event.CoversGlobalWrites (FloatLiteralsMemory.graph 64 9) [] := by
  intro h
  have hw : (FloatLiteralsMemory.graph 64 9).writeByte FloatLiteralsMemory.outputId ⟨.global,64⟩ =
      some (.realPart .f32 9 0) := by rfl
  exact List.not_mem_nil (h _ _ _ rfl hw)

end
end Ptx.StreamTests
