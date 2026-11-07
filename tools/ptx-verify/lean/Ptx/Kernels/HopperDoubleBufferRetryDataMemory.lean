import Ptx.Kernels.HopperDoubleBufferRetryDataSC

/-! Full existing MemoryConditions for explicit independent retry RF/co and
arbitrary represented inputs/frame. No memory or tensor admission is a premise.
Physical runtime, allocation/lifetime and observers remain separate. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section

theorem retry_data_memory_witness (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.MemoryConditions Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (dataInitialProxyMemory a b tiles frame) (retryDataReadWitness a b tiles schedules) (retryDataCoherenceWitness a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster := {
  toCausalConstraints := retry_data_causal_witness a b tiles schedules frame ht hb
  baseAcyclic := retry_data_memory_base_acyclic a b tiles schedules ht hb
  coherence := fun _ => retry_data_coherent_witness a b tiles schedules ht hb
  atomicity := fun _ => retry_data_single_copy_atomicity a b tiles schedules ht hb
  rmwAtomicity := fun _ => retry_data_rmw_atomicity a b tiles schedules ht hb
  scPerLocation := fun _ => retry_data_sc_per_location a b tiles schedules ht hb
}

theorem retry_data_memory_exists (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∃ rf co, Unified.MemoryConditions Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (dataInitialProxyMemory a b tiles frame) rf co (retryHistories (retryDataFamily a b tiles schedules)) dataCluster :=
  ⟨retryDataReadWitness a b tiles schedules,retryDataCoherenceWitness a b tiles schedules,retry_data_memory_witness a b tiles schedules frame ht hb⟩

end
end Ptx.Kernels.HopperDoubleBuffer
