import Ptx.Kernels.HopperDoubleBufferMemorySC

/-! Full model-relative memory conditions for independently constructed RF/co
and arbitrary represented input/frame. Source/control/TMA components were
proved separately. Observer, full-Pre refinement, allocation and runtime
correspondence remain separate obligations. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section

theorem data_memory_witness (a b tiles frame) (hb : tiles ≤ 2^28) :
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataInitialProxyMemory a b tiles frame) (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles)
      (dataHistories a b tiles) dataCluster := {
  toCausalConstraints := data_causal_witness a b tiles frame hb
  baseAcyclic := data_memory_base_acyclic a b tiles hb
  coherence := fun _ => data_coherent_witness a b tiles hb
  atomicity := fun _ => data_single_copy_atomicity a b tiles hb
  rmwAtomicity := fun _ => data_rmw_atomicity a b tiles
  scPerLocation := fun _ => data_sc_per_location a b tiles hb
}

theorem data_memory_exists (a b tiles frame) (hb : tiles ≤ 2^28) :
    ∃ rf co, Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataInitialProxyMemory a b tiles frame) rf co (dataHistories a b tiles) dataCluster :=
  ⟨dataReadWitness a b tiles,dataCoherenceWitness a b tiles,data_memory_witness a b tiles frame hb⟩

end
end Ptx.Kernels.HopperDoubleBuffer
