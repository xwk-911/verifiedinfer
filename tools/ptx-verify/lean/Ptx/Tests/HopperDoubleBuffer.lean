import Ptx.Hopper.WgmmaDescriptorEncoding
import Ptx.Kernels.HopperDoubleBufferMatmul
import Ptx.Kernels.HopperDoubleBufferProtocol
import Ptx.Kernels.HopperDoubleBufferProbeMetadata

/-! Independent mathematical/layout/protocol tests and finite actual-source
probes. This test module does not assert a full admitted kernel execution or
arbitrary-T source correctness. All floats are symbolic real fragments. -/
namespace Ptx.HopperDoubleBufferTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def nonuniformA (tile : Nat) (p : Wgmma.ACoord) : ℝ :=
  if p.2.val = p.1.val%16 then ((tile+1)*(p.1.val+1) : Nat) else 0
def nonuniformB (tile : Nat) (p : Wgmma.BCoord) : ℝ := ((tile+2)*(p.1.val+p.2.val+1) : Nat)
theorem all_tile_counts_match_specification (a b count p) : result a b count p = specification a b count p :=
  result_matches_specification a b count p
theorem ordinary_matrix_product (a b tiles p) : result (tileA a) (tileB b) tiles p = matmul a b tiles p := result_is_matmul a b tiles p
theorem nonuniform_first_three_tiles : result nonuniformA nonuniformB 3 (0,0) = 20 := by
  rw [result_matches_specification]
  norm_num [specification,nonuniformA,nonuniformB,Finset.sum_range_succ,Fin.sum_univ_succ]
theorem nonuniform_last_three_tiles : result nonuniformA nonuniformB 3 (63,7) = 29440 := by
  rw [result_matches_specification]
  norm_num [specification,nonuniformA,nonuniformB,Finset.sum_range_succ,Fin.sum_univ_succ]
theorem zero_tiles_specification (a b p) : result a b 0 p = 0 := rfl
theorem both_stage_protocols (tiles : Nat) :
    Mbarrier.run none (stageProtocol (uses tiles 0)) = some none ∧
    Mbarrier.run none (stageProtocol (uses tiles 1)) = some none := ⟨full_stage_protocol _,full_stage_protocol _⟩
theorem arbitrary_reuse_flips_parity (tile : Nat) : expectedParity (tile+2) = 1-expectedParity tile := parity_flips_on_reuse tile
theorem missing_b_completion_rejected (phase : Nat) :
    Mbarrier.run (some (readyState phase)) [.arriveExpectTx 2304,.completeTx 2048,.tryWaitParity (phase%2) true] = none :=
  first_transfer_alone_cannot_confirm phase
theorem missing_a_completion_rejected (phase : Nat) :
    Mbarrier.run (some (readyState phase)) [.arriveExpectTx 2304,.completeTx 256,.tryWaitParity (phase%2) true] = none := by
  by_cases hz : phase = 0
  · subst phase; decide
  · simp [Mbarrier.run,Mbarrier.step,Mbarrier.accept,Mbarrier.WellFormed,Mbarrier.finish,Mbarrier.limit,readyState]
theorem phase_restart_needs_observation (phase : Nat) : Mbarrier.step (some (transferredState phase)) (.arriveExpectTx 2304) = none :=
  unobserved_phase_cannot_restart phase
theorem stale_parity_on_first_reuse_rejected : Mbarrier.step (some (transferredState 1)) (.tryWaitParity 0 true) = none := by decide
theorem runtime_address_encoding (base : Nat) (hb : base < 262144) (ha : base%16 = 0) :
    Wgmma.MatrixDescriptor.Packed (Wgmma.encodeShared base) ∧ (Wgmma.MatrixDescriptor.decode (Wgmma.encodeShared base)).base = base :=
  Wgmma.runtime_descriptor_profile hb ha
theorem stage_descriptors_encode_symbols (slot : Stage) :
    aDescriptor slot = Wgmma.encodeShared (aBase slot) ∧ bDescriptor slot = Wgmma.encodeShared (bBase slot) := by
  fin_cases slot <;> decide
theorem last_b_byte_second_stage :
    Wgmma.bAddress (Wgmma.MatrixDescriptor.decode (bDescriptor 1)) (15,7) 1 = 4623 := by decide
theorem next_a_tile_last_global_byte : Tma.sourceByte (aView 65536 3) ⟨0,16⟩ 2047 = some ⟨.global,71679⟩ :=
  a_tile_source (base := 65536) (tiles := 3) (tile := 2) (offset := 2047) (by decide) (by decide)
theorem next_b_tile_last_global_byte : Tma.sourceByte (bView 131072 3) ⟨0,2⟩ 255 = some ⟨.global,131839⟩ :=
  b_tile_source (base := 131072) (tiles := 3) (tile := 2) (offset := 255) (by decide) (by decide)
theorem actual_producer_source : Unified.Produced Generated.hopper_double_buffer_gemm.program (params 3) Ptx.Kernels.HopperStage.block (probeTrace 3 0) :=
  probe_produced 3 0
theorem actual_peer_source : Unified.Produced Generated.hopper_double_buffer_gemm.program (params 3) Ptx.Kernels.HopperStage.block (probeTrace 3 1) :=
  probe_produced 3 1
theorem actual_producer_complete : Wgmma.Complete (probeTrace 3 0).final := probe_complete 3 0
theorem actual_peer_complete : Wgmma.Complete (probeTrace 3 1).final := probe_complete 3 1
theorem actual_first_reuse_wait : (probeTrace 3 0).events.filterMap waitMetadata = [(0,0,true),(8,0,true),(0,1,true)] :=
  producer_three_tile_waits
theorem actual_second_stage_reuse : (probeTrace 4 0).events.filterMap waitMetadata = [(0,0,true),(8,0,true),(0,1,true),(8,1,true)] := producer_both_stages_reused
theorem actual_parity_wrap : (probeTrace 5 0).events.filterMap waitMetadata = [(0,0,true),(8,0,true),(0,1,true),(8,1,true),(0,0,true)] := producer_parity_wraps
theorem actual_prefetch_precedes_current_mma : (probeTrace 3 0).events.filterMap orderingMetadata =
    [26,2084,2330,4388,10000,20001,26,2084,10001,20002,10002,20003] := producer_prefetch_and_reuse_order

end
end Ptx.HopperDoubleBufferTests
