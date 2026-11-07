import Ptx.Kernels.HopperDoubleBufferWriteConflicts
import Ptx.Hopper.UnifiedRankedCoherence

/-! All coherence fields for the independently chosen RF/ranked actual
writers. No coherence or complete memory execution is an input premise. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section

theorem data_coherent_witness (a b tiles) (hb : tiles ≤ 2^28) :
    Unified.Coherent Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles) := by
  apply Unified.ranked_coherent_of_write_order (dataMemoryRank tiles)
  · intro loc left right ho
    exact data_memory_byte_order_rank hb ho
  · intro loc left right lv rv hl hr hc
    exact data_memory_causality_rank hb hc
  · intro loc left right lv rv hl hr
    exact data_all_writers_order hb hl hr

end
end Ptx.Kernels.HopperDoubleBuffer
