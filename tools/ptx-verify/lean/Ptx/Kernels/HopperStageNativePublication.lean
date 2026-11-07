import Ptx.Kernels.HopperStageCompletion
import Ptx.Hopper.UnifiedVisibility

/-! Actual TMA producers publish their own bytes to every native operand read.
Both completion observation and source order to every collective member are
proved. This supplies memory edges, not a standalone full memory witness. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem actual_wait_present (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    (candidate a b).view.Present (waitId lane) := by
  have hm : (⟨.source (waitId lane),.tryWaitParity 0 true⟩ : Tma.Entry) ∈ resourceHistory := by
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_ofFn.mpr ⟨lane,rfl⟩
  exact Hopper.barrier_present (Tma.history_sound (stage_history_valid a b) hm)
theorem wait_before_mma (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Access.GenericAfter (candidate a b).view (waitId lane) (mmaId lane) := by
  apply Access.generic_program_after
  refine ⟨actual_wait_present a b lane,?_,rfl,?_⟩
  · apply (Unified.view_present_iff _ _).mpr
    simp only [Unified.Candidate.Present,actual_mma_event,Option.isSome_some]
  · dsimp only [waitId,mmaId,middleLength]
    split <;> omega
theorem a_write_location (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (offset : Fin 2048) :
    Tma.writeLocation Tma.localShared (candidate a b).view (copyId 5) offset.val = some ⟨.shared .zero,16+offset.val⟩ := by
  simp only [Tma.writeLocation,actual_copy_a,Option.bind_some]
  rw [if_pos (show offset.val < (copyA a).descriptor.bytes from offset.isLt)]
  rfl
theorem b_write_location (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (offset : Fin 256) :
    Tma.writeLocation Tma.localShared (candidate a b).view (copyId 6) offset.val = some ⟨.shared .zero,2064+offset.val⟩ := by
  simp only [Tma.writeLocation,actual_copy_b,Option.bind_some]
  rw [if_pos (show offset.val < (copyB b).descriptor.bytes from offset.isLt)]
  rfl
theorem a_operand_location (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (p : Wgmma.ACoord) (byte : Fin 2) :
    Wgmma.operandLocation .zero (calls a b 0) (.a p byte) = ⟨.shared .zero,16+(Wgmma.aOffset (p,byte)).val⟩ := by
  change (⟨.shared .zero,Wgmma.aAddress (Wgmma.MatrixDescriptor.decode 68720001025) p byte⟩ : Location) = _
  rw [Wgmma.packed_a_address shifted_a_profile,shifted_a_base]
theorem b_operand_location (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (p : Wgmma.BCoord) (byte : Fin 2) :
    Wgmma.operandLocation .zero (calls a b 0) (.b p byte) = ⟨.shared .zero,2064+(Wgmma.bOffset (p,byte)).val⟩ := by
  change (⟨.shared .zero,Wgmma.bAddress (Wgmma.MatrixDescriptor.decode 68720001153) p byte⟩ : Location) = _
  rw [Wgmma.packed_b_address shifted_b_profile,shifted_b_base]
theorem a_native_ready (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (p : Wgmma.ACoord) (byte : Fin 2) :
    Unified.TmaReady Tma.localShared (candidate a b) histories cluster (copyId 5) (Wgmma.aOffset (p,byte)).val
      (mmaId 0) (.a p byte) ⟨.shared .zero,16+(Wgmma.aOffset (p,byte)).val⟩ :=
  ⟨collective a b,a_write_location a b _,a_operand_location a b p byte,
    fun lane => ⟨waitId lane,stage_a_completion_observed a b lane,wait_before_mma a b lane⟩⟩
theorem b_native_ready (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (p : Wgmma.BCoord) (byte : Fin 2) :
    Unified.TmaReady Tma.localShared (candidate a b) histories cluster (copyId 6) (Wgmma.bOffset (p,byte)).val
      (mmaId 0) (.b p byte) ⟨.shared .zero,2064+(Wgmma.bOffset (p,byte)).val⟩ :=
  ⟨collective a b,b_write_location a b _,b_operand_location a b p byte,
    fun lane => ⟨waitId lane,stage_b_completion_observed a b lane,wait_before_mma a b lane⟩⟩
def nativeRead (operand : Wgmma.OperandByte) : Unified.Node := .wgmmaRead (mmaId 0) operand
def nativeProducer : Wgmma.OperandByte → Unified.Node
  | .a p byte => .base (.tma (.write (copyId 5) (Wgmma.aOffset (p,byte)).val))
  | .b p byte => .base (.tma (.write (copyId 6) (Wgmma.bOffset (p,byte)).val))
def nativeLocation (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (operand : Wgmma.OperandByte) : Location :=
  Wgmma.operandLocation .zero (calls a b 0) operand
theorem actual_native_publication (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (operand : Wgmma.OperandByte) :
    Unified.NativePublished Tma.localShared (candidate a b) histories cluster (nativeLocation a b operand)
      (nativeProducer operand) (nativeRead operand) := by
  cases operand with
  | a p byte => simpa only [nativeLocation,a_operand_location,nativeProducer,nativeRead,Unified.NativePublished] using a_native_ready a b p byte
  | b p byte => simpa only [nativeLocation,b_operand_location,nativeProducer,nativeRead,Unified.NativePublished] using b_native_ready a b p byte
theorem actual_native_byte_order (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (operand : Wgmma.OperandByte) :
    Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate a b) histories cluster (nativeLocation a b operand)
      (nativeProducer operand) (nativeRead operand) := Unified.native_published_byte_order (actual_native_publication a b operand)

end
end Ptx.Kernels.HopperStage
