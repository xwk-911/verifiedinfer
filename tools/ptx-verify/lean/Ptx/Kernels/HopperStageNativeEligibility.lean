import Ptx.Kernels.HopperStageRegionRules
import Ptx.Kernels.HopperStageAccessRegions
import Ptx.Hopper.UnifiedMixedSize

/-! Native eligibility is derived from the actual whole-candidate footprint
inventory and publication. No eligibility oracle or additional no-race caller
precondition is introduced. Full memory existence/control/observer remain
separate from this universal conditional visibility result. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem conflicting_footprints_equal {a b writer other loc value}
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) writer loc = some value)
    (ha : Unified.Accesses Tma.localShared Access.globalDescriptor (candidate a b) other loc) :
    Unified.SameFootprint Tma.localShared Access.globalDescriptor (candidate a b) writer other := by
  obtain ⟨wb,ws,hfw,hwreg⟩ := write_footprint_regions hw
  obtain ⟨rb,rs,hfr⟩ := Unified.access_footprint_exists ha
  have hrreg := all_footprint_regions hfr
  have hwb := Unified.access_footprint_bounds (.inr (by rw [hw]; rfl)) hfw
  have hrb := Unified.access_footprint_bounds ha hfr
  suffices he : wb = rb ∧ ws = rs by
    refine ⟨(wb,ws),hfw,?_⟩
    rw [he.1,he.2]
    exact hfr
  exact HopperStage.overlapping_regions_equal hwreg hrreg hwb hrb
theorem stage_no_mixed_size_race (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (rf : Unified.ReadsFrom) :
    ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate a b) histories cluster rf :=
  Unified.compatible_conflicts_no_mixed_size_race (fun _ _ _ _ => conflicting_footprints_equal)
theorem native_eligibility_derived (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (rf : Unified.ReadsFrom) (operand : Wgmma.OperandByte) :
    Unified.Eligible Tma.localShared Access.globalDescriptor (candidate a b) histories cluster rf (nativeRead operand) (nativeLocation a b operand) :=
  native_eligible (stage_no_mixed_size_race a b rf) operand
theorem native_rf_forced {a b initial rf co}
    (hc : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate a b) initial rf co histories cluster)
    (operand : Wgmma.OperandByte) :
    rf (nativeRead operand) (nativeLocation a b operand) = some (nativeProducer operand) :=
  native_reads_from_producer hc (stage_no_mixed_size_race a b rf) operand
theorem native_input_agreement_derived {a b initial rf co}
    (hc : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate a b) initial rf co histories cluster) :
    Wgmma.InputAgreement .zero (calls a b 0) (transferView a b) :=
  native_input_from_memory hc (stage_no_mixed_size_race a b rf)

end
end Ptx.Kernels.HopperStage
