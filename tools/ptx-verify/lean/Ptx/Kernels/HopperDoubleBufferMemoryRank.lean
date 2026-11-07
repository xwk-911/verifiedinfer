import Ptx.Kernels.HopperDoubleBufferReadWitness
import Ptx.Hopper.UnifiedMemoryControl

/-! A checked memory rank obtained from control refinement of justified byte
edges. The rank constructs witnesses; it is not added as an execution premise
and does not grant arbitrary control-to-memory visibility. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section

def dataMemoryRank (tiles : Nat) (node : Unified.Node) : Nat :=
  dataNativeControlRank tiles (Unified.memoryControlNode node)

theorem data_memory_byte_order_rank {a b tiles loc left right} (hb : tiles ≤ 2^28)
    (h : Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster loc left right) : dataMemoryRank tiles left < dataMemoryRank tiles right := by
  have hp := Unified.byte_order_control_path (block := HopperStage.block) (data_no_nonbulk a b tiles) h
  exact hp.rank_lt (dataNativeControlRank tiles) (fun _ _ => data_native_control_edge_rank hb)

theorem data_memory_base_acyclic (a b tiles) (hb : tiles ≤ 2^28) :
    ∀ loc node, ¬Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster loc node node :=
  Unified.byte_order_acyclic_of_control (data_no_nonbulk a b tiles) (data_native_control_acyclic a b tiles hb)

theorem data_memory_observed_rank {a b tiles left right} (hb : tiles ≤ 2^28)
    (he : Unified.Observed Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) (dataReadWitness a b tiles) left right) :
    dataMemoryRank tiles left < dataMemoryRank tiles right := by
  obtain ⟨_,loc,value,hr,hs,_⟩ := he
  cases right with
  | base node => cases hs
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,hcall,hl,hvalue⟩ := Unified.native_read_location hr
    obtain ⟨tile,ht,rfl,rfl⟩ := data_representative_call hcall
    subst loc
    change dataReadWitness a b tiles (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) = some left at hs
    have hw := data_read_witness_current a b tiles tile ht operand
    rw [hw] at hs
    cases hs
    exact data_memory_byte_order_rank hb (data_native_byte_order a b tiles tile ht hb operand)

theorem data_memory_observation_order_rank {a b tiles left right} (hb : tiles ≤ 2^28)
    (he : Unified.ObservationOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataReadWitness a b tiles) left right) : dataMemoryRank tiles left < dataMemoryRank tiles right := by
  induction he with
  | direct h => exact data_memory_observed_rank hb h
  | viaRMW _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem data_memory_causality_rank {a b tiles loc left right} (hb : tiles ≤ 2^28)
    (he : Unified.CausalityAt Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster (dataReadWitness a b tiles) loc left right) :
    dataMemoryRank tiles left < dataMemoryRank tiles right := by
  rcases he with ⟨_,_,hpath⟩ | ⟨middle,ho,_,_,hm⟩
  · exact data_memory_byte_order_rank hb hpath
  · exact (data_memory_observation_order_rank hb ho).trans (data_memory_byte_order_rank hb hm)

end
end Ptx.Kernels.HopperDoubleBuffer
