import Ptx.Kernels.HopperStageMemoryInventory

/-! Every native shared byte has one actual TMA producer. Native taint is
excluded by publication/unique writers; eligibility still also requires the
global no-mixed-size-race condition. RF/co are arbitrary memory witnesses.
This is not an independent full memory/observer existence theorem. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem native_producer_write (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (operand : Wgmma.OperandByte) :
    Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) (nativeProducer operand) (nativeLocation a b operand) =
      some (transferView a b (nativeLocation a b operand)) := by
  cases operand with
  | a p byte =>
    simp only [nativeProducer,nativeLocation,a_operand_location,Unified.base_write_preserved]
    apply Access.tensor_write (a_write_location a b (Wgmma.aOffset (p,byte)))
    simpa only [Tma.transferByte,actual_copy_a,Option.bind_some,copyA] using transfer_a_payload a b (Wgmma.aOffset (p,byte))
  | b p byte =>
    simp only [nativeProducer,nativeLocation,b_operand_location,Unified.base_write_preserved]
    apply Access.tensor_write (b_write_location a b (Wgmma.bOffset (p,byte)))
    simpa only [Tma.transferByte,actual_copy_b,Option.bind_some,copyB] using transfer_b_payload a b (Wgmma.bOffset (p,byte))
theorem native_producer_unique {a b operand writer value}
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (candidate a b) writer (nativeLocation a b operand) = some value) :
    writer = nativeProducer operand := by
  have hs : (nativeLocation a b operand).space = .shared .zero := by cases operand <;> rfl
  obtain ⟨id,offset,rfl,hl⟩ := shared_writer_is_tensor hs hw
  have hi := tensor_write_id_cases hl
  cases operand with
  | a p byte =>
    rw [nativeLocation,a_operand_location] at hl
    rcases hi with rfl | rfl
    · simp only [Tma.writeLocation,actual_copy_a,Option.bind_some] at hl
      split at hl
      · have ha := congrArg Location.address (Option.some.inj hl)
        have he : offset = (Wgmma.aOffset (p,byte)).val := by dsimp [Tma.localShared,copyA,Location.add] at ha; omega
        subst offset
        rfl
      · cases hl
    · simp only [Tma.writeLocation,actual_copy_b,Option.bind_some] at hl
      split at hl
      · have ha := congrArg Location.address (Option.some.inj hl)
        have ho := (Wgmma.aOffset (p,byte)).isLt
        dsimp [Tma.localShared,copyB,Location.add] at ha
        omega
      · cases hl
  | b p byte =>
    rw [nativeLocation,b_operand_location] at hl
    rcases hi with rfl | rfl
    · simp only [Tma.writeLocation,actual_copy_a,Option.bind_some] at hl
      split at hl
      · rename_i ho
        have ha := congrArg Location.address (Option.some.inj hl)
        change offset < 2048 at ho
        dsimp [Tma.localShared,copyA,Location.add] at ha
        omega
      · cases hl
    · simp only [Tma.writeLocation,actual_copy_b,Option.bind_some] at hl
      split at hl
      · have ha := congrArg Location.address (Option.some.inj hl)
        have he : offset = (Wgmma.bOffset (p,byte)).val := by dsimp [Tma.localShared,copyB,Location.add] at ha; omega
        subst offset
        rfl
      · cases hl
theorem native_not_tainted (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (rf : Unified.ReadsFrom) (operand : Wgmma.OperandByte) :
    ¬Unified.Tainted Tma.localShared Access.globalDescriptor (candidate a b) histories cluster rf (nativeRead operand) (nativeLocation a b operand) := by
  rintro (⟨writer,hw,hrace⟩ | ⟨left,right,hl,hr,hrace⟩)
  · obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hw
    have he := native_producer_unique hvalue
    subst writer
    exact hrace.notBackward (Unified.byte_order_causal hrace.right hrace.left (actual_native_byte_order a b operand))
  · obtain ⟨vl,hvl⟩ := Option.isSome_iff_exists.mp hl
    obtain ⟨vr,hvr⟩ := Option.isSome_iff_exists.mp hr
    have hleft := native_producer_unique hvl
    have hright := native_producer_unique hvr
    subst left
    subst right
    exact hrace.notStrong (Unified.write_self_strong hvl)
theorem native_eligible {a b rf} (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate a b) histories cluster rf)
    (operand : Wgmma.OperandByte) :
    Unified.Eligible Tma.localShared Access.globalDescriptor (candidate a b) histories cluster rf (nativeRead operand) (nativeLocation a b operand) :=
  ⟨hm,native_not_tainted a b rf operand⟩
theorem native_reads_from_producer {a b initial rf co}
    (hc : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate a b) initial rf co histories cluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate a b) histories cluster rf)
    (operand : Wgmma.OperandByte) : rf (nativeRead operand) (nativeLocation a b operand) = some (nativeProducer operand) := by
  exact Unified.unique_writer_source hc (native_eligible hm operand) (native_producer_write a b operand)
    (Unified.native_read_byte (actual_representative a b)) (actual_native_byte_order a b operand)
    (fun _ _ => native_producer_unique)
theorem native_input_from_memory {a b initial rf co}
    (hc : Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate a b) initial rf co histories cluster)
    (hm : ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate a b) histories cluster rf) :
    Wgmma.InputAgreement .zero (calls a b 0) (transferView a b) := by
  intro operand
  exact Unified.unique_writer_visible hc (native_eligible hm operand) (native_producer_write a b operand)
    (Unified.native_read_byte (actual_representative a b)) (actual_native_byte_order a b operand)
    (fun _ _ => native_producer_unique)

end
end Ptx.Kernels.HopperStage
