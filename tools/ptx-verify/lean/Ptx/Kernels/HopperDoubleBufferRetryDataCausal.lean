import Ptx.Kernels.HopperDoubleBufferRetryDataReadConflicts

/-! Explicit ranked coherence and causal constraints for independent retry
RF values. Selected sources precede reads and are latest among earlier actual
writers. Neither causality nor a complete memory execution is assumed. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryDataCoherenceWitness (a : TileA) (b : TileB) (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) :
    Location → Option Unified.Node → Option Unified.Node → Prop :=
  Unified.RankedCo Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) (retryDataMemoryRank a b tiles schedules)

theorem retry_data_selected_source_rank {a b tiles schedules read loc value} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) read loc = some value) :
    Unified.sourceRank (retryDataMemoryRank a b tiles schedules) (retryDataReadWitness a b tiles schedules read loc) <
      retryDataMemoryRank a b tiles schedules read+1 := by
  cases read with
  | base node => change 0 < retryDataMemoryRank a b tiles schedules (.base node)+1; omega
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,he,hl,_⟩ := Unified.native_read_location hr
    obtain ⟨tile,hi,rfl,rfl⟩ := retry_data_representative_call ht hb he
    subst loc
    change Unified.sourceRank (retryDataMemoryRank a b tiles schedules)
      (retryDataReadWitness a b tiles schedules (retryNativeRead (retryDataFamily a b tiles schedules) tile operand)
        (retryNativeLocation (retryDataFamily a b tiles schedules) tile operand)) <
      retryDataMemoryRank a b tiles schedules (retryNativeRead (retryDataFamily a b tiles schedules) tile operand)+1
    rw [retry_data_read_witness_current a b tiles schedules tile hi ht hb operand]
    simp only [Unified.sourceRank]
    exact Nat.add_lt_add_right (retry_data_memory_rf_rank ht hb hr (retry_data_read_witness_current a b tiles schedules tile hi ht hb operand)) 1

theorem retry_data_latest_source_rank {a b tiles schedules writer read loc vw vr} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) writer loc = some vw)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) read loc = some vr)
    (hbefore : retryDataMemoryRank a b tiles schedules writer < retryDataMemoryRank a b tiles schedules read) :
    retryDataMemoryRank a b tiles schedules writer+1 ≤
      Unified.sourceRank (retryDataMemoryRank a b tiles schedules) (retryDataReadWitness a b tiles schedules read loc) := by
  obtain ⟨tile,hi,operand,rfl,rfl⟩ := retry_data_read_write_pair ht hb hr hw
  rw [retry_data_read_witness_current a b tiles schedules tile hi ht hb operand]
  simp only [Unified.sourceRank]
  rcases retry_native_writer_phase (retryDataFamily a b tiles schedules)
    (retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb) (retry_data_complete a b tiles schedules ht hb)
    (retry_data_descriptors a b tiles schedules ht hb) hb hi hw with rfl | hold | hfuture
  · exact Nat.le_refl _
  · have ho := retry_data_memory_byte_order_rank ht hb hold
    omega
  · have ho := retry_data_memory_byte_order_rank ht hb hfuture
    omega

theorem retry_data_causal_witness (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.CausalConstraints Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (dataInitialProxyMemory a b tiles frame) (retryDataReadWitness a b tiles schedules) (retryDataCoherenceWitness a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster := by
  apply Unified.ranked_causal_constraints (retryDataMemoryRank a b tiles schedules)
  · exact retry_data_read_witness_value a b tiles schedules frame ht hb
  · intro loc left right _ _ he
    exact retry_data_memory_causality_rank ht hb he
  · intro read loc value hr
    exact retry_data_selected_source_rank ht hb hr
  · intro writer read loc vw vr hw hr hbefore
    exact retry_data_latest_source_rank ht hb hw hr hbefore

theorem retry_data_causal_exists (a b tiles schedules frame) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∃ rf co, Unified.CausalConstraints Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (dataInitialProxyMemory a b tiles frame) rf co (retryHistories (retryDataFamily a b tiles schedules)) dataCluster ∧
      ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
        (retryHistories (retryDataFamily a b tiles schedules)) dataCluster rf ∧
      (∀ loc node, ¬Unified.ByteOrder Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
        (retryHistories (retryDataFamily a b tiles schedules)) dataCluster loc node node) :=
  ⟨retryDataReadWitness a b tiles schedules,retryDataCoherenceWitness a b tiles schedules,retry_data_causal_witness a b tiles schedules frame ht hb,
    candidate_no_mixed_size_race hb (retry_data_source a b tiles schedules (dataRepresentedInitial a b tiles frame) ht hb)
      (retry_data_complete a b tiles schedules ht hb) (retry_data_descriptors a b tiles schedules ht hb),
    retry_data_memory_base_acyclic a b tiles schedules ht hb⟩

end
end Ptx.Kernels.HopperDoubleBuffer
