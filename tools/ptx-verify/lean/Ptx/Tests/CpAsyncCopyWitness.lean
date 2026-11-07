import Ptx.Tests.CpAsyncCopyMemory
import Ptx.Kernels.CpAsyncCopyWitness

/-! Independent legal complete source/memory/observer witness on the represented
sample. Values and the guard follow from the specification, not a chosen output.
-/
namespace Ptx.CpAsyncCopyWitnessTests
open Ptx.ISA Ptx.Ampere Ptx.CpAsyncCopyTrace Ptx.CpAsyncCopyGraph Ptx.CpAsyncCopyMemoryTests
noncomputable section

theorem sample_checked : CheckedConditions code (launch 64 128 initial) (graph 64 128 bytes answers)
    witnessRF (witnessCo 64 128 bytes answers) := checked_witness sample_pre.1 sample_input
theorem sample_observed : ObserverConstraints (graph 64 128 bytes answers) initial witnessRF (witnessCo 64 128 bytes answers)
    (witnessObservation cfg initial answers) := observer_witness cfg initial answers
theorem sample_post : CpAsyncCopySpec.Post cfg initial (witnessObservation cfg initial answers).output :=
  graph_correct sample_pre.1 sample_checked.memory sample_observed sample_size rfl

theorem copied_first_byte : (witnessObservation cfg initial answers).output ⟨.global,128⟩ = .bits (byte 7) :=
  sample_post.1 0 (by decide)
theorem copied_high_byte : (witnessObservation cfg initial answers).output ⟨.global,135⟩ = .bits (byte 255) :=
  sample_post.1 7 (by decide)
theorem preserved_guard : (witnessObservation cfg initial answers).output ⟨.global,144⟩ = .bits (byte 165) := by
  exact sample_post.2 ⟨.global,144⟩ (by unfold CpAsyncCopySpec.domain; simp [cfg])
    (by unfold CpAsyncCopySpec.InOutput; norm_num [cfg])

theorem admissible_launch_has_execution : ∃ c rf co o, CheckedConditions code (launch 64 128 initial) c rf co ∧
    ObserverConstraints c initial rf co o ∧ o.domain = CpAsyncCopySpec.domain cfg :=
  nonvacuous cfg _ sample_pre

end
end Ptx.CpAsyncCopyWitnessTests
