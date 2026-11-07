import Ptx.Kernels.HopperStageReadConflicts

/-! An independent causal witness for arbitrary represented A/B and frame.
No assumed causal execution or desired RF is a construction premise. Full
coherence/atomicity/observer admission remains distinct. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def coherenceWitness (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :=
  Unified.InitialCo Tma.localShared Access.globalDescriptor (candidate a b)
theorem stage_causal_witness (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) :
    Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate a b)
      (initialProxyMemory a b frame) readWitness (coherenceWitness a b) histories cluster := by
  refine ⟨read_witness_agreement a b frame,?_,?_,?_⟩
  · intro _ writer loc value hw
    exact ⟨rfl,writer,rfl,by rw [Unified.WritesAt,hw]; rfl⟩
  · intro _ writer read loc vw vr hw hr _ hco
    obtain ⟨issue,operand,rfl,_,_⟩ := read_write_pair hr hw
    have hh : some (nativeProducer operand) = none := hco.1
    cases hh
  · intro _ read writer loc vr vw hr hw hc _
    obtain ⟨issue,operand,rfl,rfl,rfl⟩ := read_write_pair hr hw
    have hf := memory_byte_order_rank (actual_native_byte_order a b operand)
    have hb := memory_causality_rank hc
    change memoryRank (nativeProducer operand) < 315 at hf
    change 315 < memoryRank (nativeProducer operand) at hb
    omega
theorem stage_causal_exists (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame : Location → Symbolic.Byte) :
    ∃ rf co, Unified.CausalConstraints Tma.localShared Access.globalDescriptor (candidate a b)
      (initialProxyMemory a b frame) rf co histories cluster ∧
      ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (candidate a b) histories cluster rf ∧
      (∀ loc node, ¬Unified.ByteOrder Tma.localShared Access.globalDescriptor (candidate a b) histories cluster loc node node) :=
  ⟨readWitness,coherenceWitness a b,stage_causal_witness a b frame,
    stage_no_mixed_size_race a b readWitness,memory_base_acyclic a b⟩

end
end Ptx.Kernels.HopperStage
