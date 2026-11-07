import Ptx.Kernels.AmpereTiledWitnessMma
import Ptx.Tests.AmpereTiledCorrect

/-! Independent nonuniform full-source/control/MMA witness components for four
CTAs and three K phases. The full memory/observer/SourceAligned assembly is checked separately in
AmpereTiledNonvacuous tests.
The old inconsistent oracle remains a separate negative test. -/
namespace Ptx.AmpereTiledWitnessTests
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph Ptx.AmpereTiledEvents
open Ptx.AmpereTiledPhaseTests Ptx.AmpereTiledCorrectTests
noncomputable section

abbrev selectedOracle := AmpereTiledWitnessOracle.oracle input representedLaunch left right
def candidate := AmpereTiledWitnessOracle.execution input representedLaunch left right
theorem source : SourceInfo input representedLaunch candidate := AmpereTiledWitnessOracle.source represented_pre (by constructor <;> decide)
theorem full_cta_barriers : BarrierParticipation candidate := AmpereTiledControl.barriers source
theorem all_control_acyclic : ControlAcyclic candidate := AmpereTiledControl.control source
theorem mandatory_full_warp : MmaConditions AmpereTiledGraph.code representedLaunch candidate :=
  AmpereTiledWitnessMma.mma represented_pre source.active

theorem actual_wait_rank : AmpereTiledControl.rank (.copyWrite ⟨reader,8⟩) = 110 ∧
    AmpereTiledControl.rank (.thread ⟨reader,38⟩) = 114 := by decide
theorem actual_mma_rank : AmpereTiledControl.rank (.thread ⟨reader,47⟩) = 141 ∧
    AmpereTiledControl.rank (.thread ⟨reader,48⟩) = 144 := by decide
theorem no_exit_exemptions (a b : Node) : ¬ ExitBeforeReturn candidate a b := AmpereTiledControl.no_exit_edges source a b
theorem third_phase_all_lanes (lane : Mma.Lane) :
    (AmpereTiledWitnessMma.members input representedLaunch left right reader 2 lane).Valid
      AmpereTiledGraph.code representedLaunch candidate :=
  AmpereTiledWitnessMma.participant_valid represented_pre source.active reader_valid (by decide) lane

theorem actual_last_entry_pc : sourcePC candidate AmpereTiledGraph.code representedLaunch.params representedLaunch.geometry.block
    ⟨reader,47⟩ = some 71 := by
  have he : candidate.eventAt ⟨reader,47⟩ = some (.mmaEntry (AmpereTiledWitnessMma.call input representedLaunch left right reader 2)) := by
    change (AmpereTiledWitnessOracle.execution input representedLaunch left right).eventAt ⟨reader,17*2+13⟩ = _
    rw [AmpereTiledWitnessOracle.phase_event represented_pre source.active reader_valid (by decide : 2 < input.k/16) (by decide : 13 < 17),phase_events]
    rfl
  exact mma_source_pc source.formed (.inl he)
theorem actual_last_return_pc : sourcePC candidate AmpereTiledGraph.code representedLaunch.params representedLaunch.geometry.block
    ⟨reader,48⟩ = some 71 := by
  have he : candidate.eventAt ⟨reader,48⟩ = some (.mmaReturn (AmpereTiledWitnessMma.call input representedLaunch left right reader 2)) := by
    change (AmpereTiledWitnessOracle.execution input representedLaunch left right).eventAt ⟨reader,17*2+14⟩ = _
    rw [AmpereTiledWitnessOracle.phase_event represented_pre source.active reader_valid (by decide : 2 < input.k/16) (by decide : 14 < 17),phase_events]
    rfl
  exact mma_source_pc source.formed (.inr he)

theorem a_query_actual : (selectedOracle reader).word32 26 = .packed ⟨3146,3147⟩ := by
  change (AmpereTiledWitnessOracle.oracle input representedLaunch left right reader).word32 (10*2+3+(3 : Fin 4).val) = _
  rw [AmpereTiledWitnessOracle.a_query input representedLaunch left right reader 2 3]
  congr 1
  norm_num [AmpereTiledWitnessOracle.aPair,AmpereTiledWitnessOracle.lane,Mma.packA,Mma.gatherA,tileA,Mma.aCoord,reader,left]
theorem b_query_actual : (selectedOracle reader).word32 28 = .packed ⟨46015,47015⟩ := by
  change (AmpereTiledWitnessOracle.oracle input representedLaunch left right reader).word32 (10*2+7+(1 : Fin 2).val) = _
  rw [AmpereTiledWitnessOracle.b_query input representedLaunch left right reader 2 1]
  congr 1
  norm_num [AmpereTiledWitnessOracle.bPair,AmpereTiledWitnessOracle.lane,Mma.packB,Mma.gatherB,tileB,Mma.bCoord,reader,right]
theorem initial_copy_byte_actual : (AmpereTiledWitnessOracle.payload input representedLaunch reader 2 1)[4]? =
    some (.realPart .f16 3146 0) := by
  have hb := AmpereTiledWitnessOracle.payload_byte input representedLaunch reader 2 1 4
  norm_num [AmpereTiledBounds.copyStart,context,input,AmpereTiledSourceTests.cfg,reader,representedLaunch,
    AmpereTiledCorrectTests.initial,left] at hb
  exact hb
theorem final_answer_is_product : (selectedOracle reader).matrix 29 3 = product left right 31 15 48 := rfl
theorem nonuniform_final_answer : (selectedOracle reader).matrix 29 3 = 3534768920 := by
  rw [final_answer_is_product]
  norm_num [product,left,right,Finset.sum_range_succ]

def zeroLaunch : Scalar.Launch := ⟨geometry AmpereTiledSourceTests.zeroK,params AmpereTiledSourceTests.zeroK,fun _ => .bits (byte 165)⟩
theorem zero_pre : Pre AmpereTiledSourceTests.zeroK left right zeroLaunch :=
  ⟨AmpereTiledSourceTests.zero_k_layout,zero_k_no_input rfl left right _,rfl,rfl⟩
theorem zero_k_source : SourceInfo AmpereTiledSourceTests.zeroK zeroLaunch
    (AmpereTiledWitnessOracle.execution AmpereTiledSourceTests.zeroK zeroLaunch left right) :=
  AmpereTiledWitnessOracle.source zero_pre AmpereTiledSourceTests.zero_active
theorem zero_k_mma : MmaConditions AmpereTiledGraph.code zeroLaunch
    (AmpereTiledWitnessOracle.execution AmpereTiledSourceTests.zeroK zeroLaunch left right) :=
  AmpereTiledWitnessMma.mma zero_pre AmpereTiledSourceTests.zero_active

end
end Ptx.AmpereTiledWitnessTests
