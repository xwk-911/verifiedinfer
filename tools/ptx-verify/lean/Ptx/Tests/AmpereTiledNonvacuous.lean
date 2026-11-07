import Ptx.Kernels.AmpereTiledNonvacuous
import Ptx.Tests.AmpereTiledWitnessMemory

/-! Full checked admission, actual barrier PCs, and correctness on a nonuniform
four-CTA/three-phase instance, zero K and both inactive source-return paths. -/
namespace Ptx.AmpereTiledNonvacuousTests
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph
open Ptx.AmpereTiledPhaseTests Ptx.AmpereTiledCorrectTests Ptx.AmpereTiledWitnessTests Ptx.AmpereTiledWitnessMemoryTests
noncomputable section

theorem full_pre_nonvacuous (cfg : Config) (a b : Matrix) :
    CheckedNonvacuous AmpereTiledGraph.code (Pre cfg a b) (fun _ => domain cfg) :=
  AmpereTiledNonvacuous.nonvacuous cfg a b

theorem nonuniform_checked : CheckedConditions AmpereTiledGraph.code representedLaunch candidate witnessRF witnessCo :=
  AmpereTiledNonvacuous.active_checked represented_pre AmpereTiledWitnessTests.source.active

theorem nonuniform_legal_complete : CheckedConditions AmpereTiledGraph.code representedLaunch candidate witnessRF witnessCo ∧
    ObserverConstraints candidate representedLaunch.initial witnessRF witnessCo finalObserver ∧ finalObserver.domain = domain input :=
  ⟨nonuniform_checked,admitted_observer,observer_domain⟩

theorem nonuniform_checked_post : Post input left right representedLaunch.initial finalObserver.output :=
  universal_contract representedLaunch candidate witnessRF witnessCo finalObserver represented_pre
    nonuniform_checked admitted_observer observer_domain

theorem all_actual_barrier_sites {phase : Nat} (hp : phase < 3) (half offset : Fin 2) :
    sourcePC candidate AmpereTiledGraph.code representedLaunch.params representedLaunch.geometry.block
      ⟨reader,17*phase+5+10*half.val+offset.val⟩ = some (64+8*half.val) :=
  AmpereTiledBarrierSources.barrier_pc AmpereTiledWitnessTests.source reader_valid hp half offset

theorem third_phase_pre_arrival_pc : sourcePC candidate AmpereTiledGraph.code representedLaunch.params representedLaunch.geometry.block
    ⟨reader,39⟩ = some 64 := all_actual_barrier_sites (by decide : 2 < 3) 0 0
theorem third_phase_pre_return_pc : sourcePC candidate AmpereTiledGraph.code representedLaunch.params representedLaunch.geometry.block
    ⟨reader,40⟩ = some 64 := all_actual_barrier_sites (by decide : 2 < 3) 0 1
theorem third_phase_post_arrival_pc : sourcePC candidate AmpereTiledGraph.code representedLaunch.params representedLaunch.geometry.block
    ⟨reader,49⟩ = some 72 := all_actual_barrier_sites (by decide : 2 < 3) 1 0
theorem third_phase_post_return_pc : sourcePC candidate AmpereTiledGraph.code representedLaunch.params representedLaunch.geometry.block
    ⟨reader,50⟩ = some 72 := all_actual_barrier_sites (by decide : 2 < 3) 1 1

theorem pre_post_cannot_match : ¬ BarrierSync candidate (.thread ⟨reader,39⟩) (.thread ⟨reader,50⟩) := by
  rintro ⟨_,bid,generation,ha,hb⟩
  obtain ⟨pa,_,ia,_,hga,hsa⟩ := AmpereTiledControl.arrival_info AmpereTiledWitnessTests.source ha
  obtain ⟨pb,_,ib,_,hgb,hsb⟩ := AmpereTiledControl.return_info AmpereTiledWitnessTests.source hb
  change 39 = 17*pa+5+10*ia.val at hsa
  change 50 = 17*pb+6+10*ib.val at hsb
  have hi := ia.isLt
  have hj := ib.isLt
  omega

theorem same_site_wrong_generation_cannot_match : ¬ BarrierSync candidate (.thread ⟨reader,39⟩) (.thread ⟨reader,23⟩) := by
  rintro ⟨_,bid,generation,ha,hb⟩
  obtain ⟨pa,_,ia,_,hga,hsa⟩ := AmpereTiledControl.arrival_info AmpereTiledWitnessTests.source ha
  obtain ⟨pb,_,ib,_,hgb,hsb⟩ := AmpereTiledControl.return_info AmpereTiledWitnessTests.source hb
  change 39 = 17*pa+5+10*ia.val at hsa
  change 23 = 17*pb+6+10*ib.val at hsb
  have hi := ia.isLt
  have hj := ib.isLt
  omega

theorem zero_k_checked : CheckedConditions AmpereTiledGraph.code zeroLaunch
    (AmpereTiledWitnessOracle.execution AmpereTiledSourceTests.zeroK zeroLaunch left right)
    witnessRF (AmpereTiledWitnessMemory.co AmpereTiledSourceTests.zeroK zeroLaunch left right) :=
  AmpereTiledNonvacuous.active_checked zero_pre AmpereTiledSourceTests.zero_active

def inactive (emptyRows : Bool) : Config :=
  if emptyRows then ⟨0,8,16,1,3,5,8⟩ else ⟨16,0,16,1,1,1,8⟩
def inactiveLaunch (emptyRows : Bool) : Scalar.Launch :=
  ⟨geometry (inactive emptyRows),params (inactive emptyRows),fun _ => .bits (byte 165)⟩
theorem inactive_not_active (emptyRows : Bool) : ¬ Active (inactive emptyRows) := by
  cases emptyRows <;> simp [inactive,Active]
theorem inactive_pre (emptyRows : Bool) : Pre (inactive emptyRows) left right (inactiveLaunch emptyRows) := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,rfl,rfl⟩
  · cases emptyRows <;> decide
  · cases emptyRows <;> decide
  · cases emptyRows <;> decide
  · cases emptyRows <;> decide
  · intro ha
    exact (inactive_not_active emptyRows ha).elim
  · intro ha
    exact (inactive_not_active emptyRows ha).elim
  · intro ha
    exact (inactive_not_active emptyRows ha).elim

theorem inactive_checked (emptyRows : Bool) : CheckedConditions AmpereTiledGraph.code (inactiveLaunch emptyRows)
    (AmpereTiledWitnessInactive.execution (inactive emptyRows) (inactiveLaunch emptyRows))
    AmpereTiledWitnessInactive.rf (AmpereTiledWitnessInactive.co (inactive emptyRows) (inactiveLaunch emptyRows)) :=
  AmpereTiledWitnessInactive.checked (inactive_pre emptyRows) (inactive_not_active emptyRows)

theorem inactive_observer (emptyRows : Bool) : ObserverConstraints
    (AmpereTiledWitnessInactive.execution (inactive emptyRows) (inactiveLaunch emptyRows)) (inactiveLaunch emptyRows).initial
    AmpereTiledWitnessInactive.rf (AmpereTiledWitnessInactive.co (inactive emptyRows) (inactiveLaunch emptyRows))
    (AmpereTiledWitnessInactive.observation (inactive emptyRows) (inactiveLaunch emptyRows)) :=
  AmpereTiledWitnessInactive.observer _ _

theorem inactive_checked_post (emptyRows : Bool) : Post (inactive emptyRows) left right (inactiveLaunch emptyRows).initial
    (AmpereTiledWitnessInactive.observation (inactive emptyRows) (inactiveLaunch emptyRows)).output :=
  AmpereTiledCorrect.correct _ left right _ _ _ _ _ (inactive_pre emptyRows) (inactive_checked emptyRows) (inactive_observer emptyRows) rfl

theorem inactive_source_counts (emptyRows : Bool) (id : ThreadId) :
    (AmpereTiledWitnessInactive.trace (inactive emptyRows) (inactiveLaunch emptyRows) id).count =
      if emptyRows then 15 else 17 := by cases emptyRows <;> rfl

theorem inactive_no_events (emptyRows : Bool) (event) :
    (AmpereTiledWitnessInactive.execution (inactive emptyRows) (inactiveLaunch emptyRows)).eventAt event = none :=
  AmpereTiledWitnessInactive.event_none _ _ _

end
end Ptx.AmpereTiledNonvacuousTests
