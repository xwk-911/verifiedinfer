import Ptx.Kernels.AmpereTiledWitnessComponents
import Ptx.Tests.AmpereTiledWitness

/-! Actual nonuniform source/rf/co/observer instances. Matrix/frame values are
derived after constructing admission, rather than being fed into a witness.
The complete checked witness is assembled separately in AmpereTiledNonvacuous. -/
namespace Ptx.AmpereTiledWitnessMemoryTests
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph
open Ptx.AmpereTiledPhaseTests Ptx.AmpereTiledCorrectTests Ptx.AmpereTiledWitnessTests
noncomputable section

abbrev witnessRF := AmpereTiledWitnessMemory.rf
abbrev witnessCo := AmpereTiledWitnessMemory.co input representedLaunch left right
def finalObserver := AmpereTiledWitnessObservation.observation input representedLaunch left right
theorem admitted_memory : MemoryConstraints candidate representedLaunch.initial witnessRF witnessCo :=
  AmpereTiledWitnessMemory.memory represented_pre AmpereTiledWitnessTests.source.active
theorem admitted_observer : ObserverConstraints candidate representedLaunch.initial witnessRF witnessCo finalObserver :=
  AmpereTiledWitnessObservation.observer represented_pre AmpereTiledWitnessTests.source.active
theorem observer_domain : finalObserver.domain = domain input :=
  AmpereTiledWitnessObservation.observed_domain input representedLaunch left right

theorem current_read_source : witnessRF (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ = some (.copyWrite ⟨writer,3⟩) := rfl
theorem future_read_source_rejected : witnessRF (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ ≠ some (.copyWrite ⟨writer,6⟩) := by decide
theorem current_copy_value : candidate.writeByte (.copyWrite ⟨writer,3⟩) ⟨.shared reader.cta,236⟩ = some (.realPart .f16 2322 0) := by
  have hb := AmpereTiledWitnessAccesses.copy_write_byte represented_pre AmpereTiledWitnessTests.source.active writer_valid (by decide : 1 < input.k/16) 0 4
  norm_num [AmpereTiledSharedWriters.copyBase,AmpereTiledBounds.copyStart,context,input,AmpereTiledSourceTests.cfg,
    writer,representedLaunch,AmpereTiledCorrectTests.initial,left] at hb
  exact hb
theorem actual_shared_read : candidate.readByte (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ = some (.realPart .f16 2322 0) := by
  obtain ⟨observed,hr⟩ := AmpereTiledAccesses.read_byte_exists AmpereTiledWitnessTests.source reader_valid (by decide : 1 < input.k/16) 0 0
  change candidate.readByte (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ = some observed at hr
  have hw := admitted_memory.agreement (Node.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩ observed
    (AmpereTiledRace.eligible AmpereTiledWitnessTests.source witnessRF (.thread ⟨reader,24⟩) ⟨.shared reader.cta,236⟩) hr
  rw [current_read_source] at hw
  change candidate.writeByte (.copyWrite ⟨writer,3⟩) ⟨.shared reader.cta,236⟩ = some observed at hw
  rw [current_copy_value] at hw
  exact hr.trans hw.symm

theorem old_before_current : witnessCo ⟨.shared reader.cta,236⟩ (some (.copyWrite ⟨writer,0⟩)) (some (.copyWrite ⟨writer,3⟩)) := by
  obtain ⟨old,ho⟩ := AmpereTiledAccesses.copy_write_byte_exists AmpereTiledWitnessTests.source writer_valid (by decide : 0 < input.k/16) 0 4
  change candidate.writeByte (.copyWrite ⟨writer,0⟩) ⟨.shared reader.cta,236⟩ = some old at ho
  refine ⟨?_,?_,by decide⟩
  · change (candidate.writeByte (.copyWrite ⟨writer,0⟩) ⟨.shared reader.cta,236⟩).isSome = true
    rw [ho]
    rfl
  · change (candidate.writeByte (.copyWrite ⟨writer,3⟩) ⟨.shared reader.cta,236⟩).isSome = true
    rw [current_copy_value]
    rfl
theorem current_before_future : witnessCo ⟨.shared reader.cta,236⟩ (some (.copyWrite ⟨writer,3⟩)) (some (.copyWrite ⟨writer,6⟩)) := by
  obtain ⟨future,hf⟩ := AmpereTiledAccesses.copy_write_byte_exists AmpereTiledWitnessTests.source writer_valid (by decide : 2 < input.k/16) 0 4
  change candidate.writeByte (.copyWrite ⟨writer,6⟩) ⟨.shared reader.cta,236⟩ = some future at hf
  refine ⟨?_,?_,by decide⟩
  · change (candidate.writeByte (.copyWrite ⟨writer,3⟩) ⟨.shared reader.cta,236⟩).isSome = true
    rw [current_copy_value]
    rfl
  · change (candidate.writeByte (.copyWrite ⟨writer,6⟩) ⟨.shared reader.cta,236⟩).isSome = true
    rw [hf]
    rfl
theorem current_not_before_old : ¬ witnessCo ⟨.shared reader.cta,236⟩ (some (.copyWrite ⟨writer,3⟩)) (some (.copyWrite ⟨writer,0⟩)) := by
  intro hc
  have hr := MemoryGraph.ranked_co_write_lt hc
  norm_num [AmpereTiledControl.rank] at hr

theorem observed_post : Post input left right representedLaunch.initial finalObserver.output :=
  AmpereTiledAccumulation.active_post AmpereTiledWitnessTests.source admitted_memory represented_input mandatory_full_warp admitted_observer observer_domain
theorem observed_last_result : finalObserver.output ⟨.global,18428⟩ = .realPart .f32 3534768920 0 := by
  have hv := observed_post.1 31 15 (by decide) (by decide) 0 (by decide)
  have hp : product left right 31 15 48 = 3534768920 := final_answer_is_product.symm.trans nonuniform_final_answer
  simpa only [cLocation,Location.add,input,AmpereTiledSourceTests.cfg,hp] using hv
theorem output_padding_preserved : finalObserver.output ⟨.global,18432⟩ = .bits (byte 165) := by
  have hv := observed_post.2 ⟨.global,18432⟩ AmpereTiledMemoryTests.first_padding_in_domain AmpereTiledMemoryTests.first_padding_not_output
  simpa [representedLaunch,AmpereTiledCorrectTests.initial] using hv

theorem zero_k_memory : MemoryConstraints
    (AmpereTiledWitnessOracle.execution AmpereTiledSourceTests.zeroK zeroLaunch left right)
    zeroLaunch.initial witnessRF (AmpereTiledWitnessMemory.co AmpereTiledSourceTests.zeroK zeroLaunch left right) :=
  AmpereTiledWitnessMemory.memory zero_pre AmpereTiledSourceTests.zero_active
theorem zero_k_observer : ObserverConstraints
    (AmpereTiledWitnessOracle.execution AmpereTiledSourceTests.zeroK zeroLaunch left right)
    zeroLaunch.initial witnessRF (AmpereTiledWitnessMemory.co AmpereTiledSourceTests.zeroK zeroLaunch left right)
      (AmpereTiledWitnessObservation.observation AmpereTiledSourceTests.zeroK zeroLaunch left right) :=
  AmpereTiledWitnessObservation.observer zero_pre AmpereTiledSourceTests.zero_active

end
end Ptx.AmpereTiledWitnessMemoryTests
