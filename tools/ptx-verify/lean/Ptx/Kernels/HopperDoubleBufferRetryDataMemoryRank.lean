import Ptx.Kernels.HopperDoubleBufferRetryDataReads
import Ptx.Hopper.UnifiedMemoryControl

/-! Constructed retry memory rank from one-way control refinement of already
justified byte edges. This adds neither visibility nor an admission premise. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def retryDataMemoryRank (a : TileA) (b : TileB) (tiles : Nat) (schedules : Wgmma.Lane → Nat → Nat) (node : Unified.Node) : Nat :=
  retryUnifiedRank (retryDataFamily a b tiles schedules) (Unified.memoryControlNode node)

theorem retry_data_memory_byte_order_rank {a b tiles schedules loc left right} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (he : Unified.ByteOrder Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster loc left right) :
    retryDataMemoryRank a b tiles schedules left < retryDataMemoryRank a b tiles schedules right := by
  have hw := retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb
  have hc := retry_data_complete a b tiles schedules ht hb
  have hp := Unified.byte_order_control_path (block := HopperStage.block) (candidate_no_nonbulk hb hw hc) he
  exact hp.rank_lt (retryUnifiedRank (retryDataFamily a b tiles schedules))
    (fun _ _ => retry_unified_edge_order (retryDataFamily a b tiles schedules) ht hb hw)

theorem retry_data_memory_base_acyclic (a b tiles schedules) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∀ loc node, ¬Unified.ByteOrder Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster loc node node := by
  intro loc node hp
  exact Nat.lt_irrefl _ (retry_data_memory_byte_order_rank ht hb hp)

theorem retry_data_memory_rf_rank {a b tiles schedules read writer loc value} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) read loc = some value)
    (hs : retryDataReadWitness a b tiles schedules read loc = some writer) :
    retryDataMemoryRank a b tiles schedules writer < retryDataMemoryRank a b tiles schedules read := by
  cases read with
  | base node => cases hs
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,he,hl,_⟩ := Unified.native_read_location hr
    obtain ⟨tile,hi,rfl,rfl⟩ := retry_data_representative_call ht hb he
    subst loc
    change retryDataReadWitness a b tiles schedules (retryNativeRead (retryDataFamily a b tiles schedules) tile operand)
      (retryNativeLocation (retryDataFamily a b tiles schedules) tile operand) = some writer at hs
    rw [retry_data_read_witness_current a b tiles schedules tile hi ht hb operand] at hs
    cases hs
    exact retry_data_memory_byte_order_rank ht hb (retry_native_byte_order (retryDataFamily a b tiles schedules) ht
      (retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb)
      (retry_data_descriptors a b tiles schedules ht hb) tile hi operand)

theorem retry_data_memory_observed_rank {a b tiles schedules left right} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (he : Unified.Observed Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryDataReadWitness a b tiles schedules) left right) :
    retryDataMemoryRank a b tiles schedules left < retryDataMemoryRank a b tiles schedules right := by
  obtain ⟨_,loc,value,hr,hs,_⟩ := he
  exact retry_data_memory_rf_rank ht hb hr hs

theorem retry_data_memory_observation_order_rank {a b tiles schedules left right} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (he : Unified.ObservationOrder Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryDataReadWitness a b tiles schedules) left right) :
    retryDataMemoryRank a b tiles schedules left < retryDataMemoryRank a b tiles schedules right := by
  induction he with
  | direct h => exact retry_data_memory_observed_rank ht hb h
  | viaRMW _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem retry_data_memory_causality_rank {a b tiles schedules loc left right} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (he : Unified.CausalityAt Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryHistories (retryDataFamily a b tiles schedules)) dataCluster (retryDataReadWitness a b tiles schedules) loc left right) :
    retryDataMemoryRank a b tiles schedules left < retryDataMemoryRank a b tiles schedules right := by
  rcases he with ⟨_,_,hp⟩ | ⟨middle,ho,_,_,hm⟩
  · exact retry_data_memory_byte_order_rank ht hb hp
  · exact (retry_data_memory_observation_order_rank ht hb ho).trans (retry_data_memory_byte_order_rank ht hb hm)

theorem retry_data_memory_program_order_rank {a b tiles schedules left right} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (he : Unified.ProgramOrder (retryDataCandidate a b tiles schedules) left right) :
    retryDataMemoryRank a b tiles schedules left < retryDataMemoryRank a b tiles schedules right :=
  retry_unified_edge_order (retryDataFamily a b tiles schedules) ht hb
    (retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb) (Unified.program_order_control_edge he)

end
end Ptx.Kernels.HopperDoubleBuffer
