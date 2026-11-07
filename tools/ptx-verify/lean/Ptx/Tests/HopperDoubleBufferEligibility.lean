import Ptx.Kernels.HopperDoubleBufferReadWitness
import Ptx.Tests.HopperDoubleBufferData

/-! Actual footprints of all access classes, derived native eligibility and
an independent RF/value witness. No full memory/observer witness is asserted.
Finite rejection checks project only addresses, sizes and source IDs. -/
namespace Ptx.HopperDoubleBufferEligibilityTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

abbrev a := HopperDoubleBufferDataTests.a
abbrev b := HopperDoubleBufferDataTests.b
def footprint (tiles : Nat) (node : Unified.Node) : Option (Location × Nat) :=
  (Unified.kind Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) node).bind Ptx.Event.Kind.footprint
def sourceNode (tiles : Nat) (lane : Wgmma.Lane) (serial : Nat) : Unified.Node := .base (.tma (.source ⟨(ctx tiles lane).id,serial⟩))
def regionAllowed (base : Location) (size : Nat) : Bool := @decide (HopperStage.Region base size)
  (by unfold HopperStage.Region HopperStage.SharedByte HopperStage.OutputWord; infer_instance)
theorem region_allowed_iff (base : Location) (size : Nat) : regionAllowed base size = true ↔ HopperStage.Region base size := by
  unfold regionAllowed
  simp only [decide_eq_true_eq]
def selectedProducer (tiles tile : Nat) (operand : Wgmma.OperandByte) : Option (Nat × Nat) :=
  match dataReadWitness a b tiles (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) with
  | some (.base (.tma (.write copy offset))) => some (copy.issue.serial,offset)
  | _ => none

theorem actual_output_word : footprint 3 (sourceNode 3 0 35) = some (⟨.global,8192⟩,4) := by decide
theorem zero_round_output_word : footprint 0 (sourceNode 0 0 5) = some (⟨.global,8192⟩,4) := by decide
theorem actual_descriptor_footprints : footprint 3 (.base (.tma (.descriptor (dataCopyAId a b 3 2)))) = some (⟨.global,4096⟩,128) ∧
    footprint 3 (.base (.tma (.descriptor (dataCopyBId a b 3 2)))) = some (⟨.global,4224⟩,128) := by decide
theorem actual_input_footprints : footprint 3 (.base (.tma (.read (dataCopyAId a b 3 2) 2047))) = some (⟨.global,71679⟩,1) ∧
    footprint 3 (.base (.tma (.read (dataCopyBId a b 3 2) 255))) = some (⟨.global,72447⟩,1) := by decide
theorem actual_shared_write_footprint : footprint 3 (.base (.tma (.write (dataCopyAId a b 3 2) 2047))) = some (⟨.shared .zero,2063⟩,1) := by decide
theorem actual_native_footprint : footprint 3 (dataNativeRead a b 3 2 (.b (15,7) 1)) = some (⟨.shared .zero,2319⟩,1) := by decide
theorem notification_has_no_footprint : footprint 3 (.base (.tma (.notify (dataCopyAId a b 3 2)))) = none := by decide
theorem cta_has_no_footprint : footprint 3 (sourceNode 3 0 39) = none := by decide
theorem nonbulk_has_no_footprint : footprint 3 (.base (.copyRead ⟨(ctx 3 0).id,6⟩)) = none := by decide
theorem valid_region_boundaries : regionAllowed ⟨.global,8192⟩ 4 = true ∧ regionAllowed ⟨.global,10236⟩ 4 = true ∧
    regionAllowed ⟨.global,65536⟩ 1 = true ∧ regionAllowed ⟨.global,4224⟩ 128 = true := by decide
theorem invalid_output_regions : regionAllowed ⟨.global,8193⟩ 4 = false ∧ regionAllowed ⟨.global,10240⟩ 4 = false ∧
    regionAllowed ⟨.global,8192⟩ 1 = false := by decide
theorem invalid_wide_regions : regionAllowed ⟨.shared .zero,16⟩ 4 = false ∧ regionAllowed ⟨.global,8192⟩ 8 = false ∧
    regionAllowed ⟨.global,65536⟩ 4 = false := by decide
theorem invalid_initial_regions : regionAllowed ⟨.global,65535⟩ 1 = false ∧ regionAllowed ⟨.global,4225⟩ 128 = false := by decide
theorem initial_and_reused_rf : selectedProducer 3 0 (.a (0,0) 0) = some (6,0) ∧ selectedProducer 3 2 (.a (0,0) 0) = some (20,0) := by decide
theorem reused_b_rf : selectedProducer 3 2 (.b (15,7) 1) = some (21,255) := by decide

theorem arbitrary_real_mixed_size_exclusion (x : TileA) (y : TileB) (tiles : Nat) (hb : tiles ≤ 2^28) (rf : Unified.ReadsFrom) :
    ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles) (dataHistories x y tiles) dataCluster rf :=
  data_no_mixed_size_race x y tiles hb rf
theorem arbitrary_real_eligibility (x : TileA) (y : TileB) (tiles tile : Nat) (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (rf : Unified.ReadsFrom) (operand : Wgmma.OperandByte) :
    Unified.Eligible Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles) (dataHistories x y tiles)
      dataCluster rf (dataNativeRead x y tiles tile operand) (dataNativeLocation x y tiles tile operand) :=
  data_native_eligibility_derived x y tiles tile ht hb rf operand
theorem zero_round_mixed_size_exclusion (rf : Unified.ReadsFrom) :
    ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 0) (dataHistories a b 0) dataCluster rf :=
  data_no_mixed_size_race a b 0 (by decide) rf
theorem current_rf_without_race_premise {initial rf co}
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b 3)
      initial rf co (dataHistories a b 3) dataCluster) (operand : Wgmma.OperandByte) :
    rf (dataNativeRead a b 3 2 operand) (dataNativeLocation a b 3 2 operand) = some (dataNativeProducer a b 3 2 operand) :=
  data_native_rf_forced (a := a) (b := b) (tiles := 3) (tile := 2) (by decide) (by decide) hc operand
theorem arbitrary_real_value_agreement (x : TileA) (y : TileB) (tiles : Nat) (hb : tiles ≤ 2^28) (frame : Location → Symbolic.Byte) :
    Unified.ReadAgreement Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles) (dataInitialProxyMemory x y tiles frame)
      (Unified.Eligible Tma.localShared Access.globalDescriptor (dataCompleteCandidate x y tiles) (dataHistories x y tiles)
        dataCluster (dataReadWitness x y tiles)) (dataReadWitness x y tiles) :=
  data_read_witness_agreement x y tiles frame hb
theorem global_reads_choose_initial (node : Access.Node) (loc : Location) : dataReadWitness a b 3 (.base node) loc = none := rfl
theorem native_reads_choose_current (operand : Wgmma.OperandByte) :
    dataReadWitness a b 3 (dataNativeRead a b 3 2 operand) (dataNativeLocation a b 3 2 operand) = some (dataNativeProducer a b 3 2 operand) :=
  data_read_witness_current a b 3 2 (by decide) operand

end
end Ptx.HopperDoubleBufferEligibilityTests
