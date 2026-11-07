import Ptx.Kernels.HopperDoubleBufferReadConflicts

/-! Independent RF/co causal witness for arbitrary represented inputs/frame.
The coherence relation is ranked actual writers, not the invalid initial-only
relation. This record does not yet prove full coherence/atomicity/SC/observer
admission; no rank premise is added to the allowed-execution semantics. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def dataCoherenceWitness (a : TileA) (b : TileB) (tiles : Nat) : Location → Option Unified.Node → Option Unified.Node → Prop :=
  Unified.RankedCo Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) (dataMemoryRank tiles)

theorem data_selected_source_rank {a b tiles read loc value} (hb : tiles ≤ 2^28)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) read loc = some value) :
    Unified.sourceRank (dataMemoryRank tiles) (dataReadWitness a b tiles read loc) < dataMemoryRank tiles read+1 := by
  cases read with
  | base node => change 0 < dataMemoryRank tiles (.base node)+1; omega
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,he,hl,_⟩ := Unified.native_read_location hr
    obtain ⟨tile,ht,rfl,rfl⟩ := data_representative_call he
    subst loc
    change Unified.sourceRank (dataMemoryRank tiles)
      (dataReadWitness a b tiles (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand)) <
        dataMemoryRank tiles (dataNativeRead a b tiles tile operand)+1
    rw [data_read_witness_current a b tiles tile ht operand]
    simp only [Unified.sourceRank]
    have ho := data_memory_byte_order_rank hb (data_native_byte_order a b tiles tile ht hb operand)
    omega

theorem data_latest_source_rank {a b tiles writer read loc vw vr} (hb : tiles ≤ 2^28)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) writer loc = some vw)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) read loc = some vr)
    (hbefore : dataMemoryRank tiles writer < dataMemoryRank tiles read) :
    dataMemoryRank tiles writer+1 ≤ Unified.sourceRank (dataMemoryRank tiles) (dataReadWitness a b tiles read loc) := by
  obtain ⟨tile,ht,operand,rfl,rfl⟩ := data_read_write_pair hb hr hw
  rw [data_read_witness_current a b tiles tile ht operand]
  simp only [Unified.sourceRank]
  rcases data_native_writer_phase ht hb hw with rfl | hold | hfuture
  · exact Nat.le_refl _
  · have ho := data_memory_byte_order_rank hb hold
    omega
  · have ho := data_memory_byte_order_rank hb hfuture
    omega

theorem data_causal_witness (a b tiles frame) (hb : tiles ≤ 2^28) :
    Unified.CausalConstraints Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataInitialProxyMemory a b tiles frame) (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles)
      (dataHistories a b tiles) dataCluster := by
  apply Unified.ranked_causal_constraints (dataMemoryRank tiles)
  · exact data_read_witness_value a b tiles frame hb
  · intro loc left right _ _ hcausal
    exact data_memory_causality_rank hb hcausal
  · intro read loc value hr
    exact data_selected_source_rank hb hr
  · intro writer read loc vw vr hw hr hbefore
    exact data_latest_source_rank hb hw hr hbefore

theorem data_causal_exists (a b tiles frame) (hb : tiles ≤ 2^28) :
    ∃ rf co, Unified.CausalConstraints Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
        (dataInitialProxyMemory a b tiles frame) rf co (dataHistories a b tiles) dataCluster ∧
      ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) (dataHistories a b tiles) dataCluster rf ∧
      (∀ loc node, ¬Unified.ByteOrder Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
        (dataHistories a b tiles) dataCluster loc node node) :=
  ⟨dataReadWitness a b tiles,dataCoherenceWitness a b tiles,data_causal_witness a b tiles frame hb,
    data_no_mixed_size_race a b tiles hb (dataReadWitness a b tiles),data_memory_base_acyclic a b tiles hb⟩

end
end Ptx.Kernels.HopperDoubleBuffer
