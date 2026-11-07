import Ptx.Kernels.HopperDoubleBufferRetryDataAtomicity

/-! Actual communication edges increase the constructed retry memory rank.
Per-location SC follows without assuming SC or an admitted execution. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_data_memory_from_read_rank {a b tiles schedules read writer loc value} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) read loc = some value)
    (hc : retryDataCoherenceWitness a b tiles schedules loc (retryDataReadWitness a b tiles schedules read loc) (some writer)) :
    retryDataMemoryRank a b tiles schedules read < retryDataMemoryRank a b tiles schedules writer := by
  obtain ⟨vw,hw⟩ := Option.isSome_iff_exists.mp hc.2.1
  obtain ⟨tile,hi,operand,rfl,rfl⟩ := retry_data_read_write_pair ht hb hr hw
  rw [retry_data_read_witness_current a b tiles schedules tile hi ht hb operand] at hc
  have hco : retryDataMemoryRank a b tiles schedules (retryNativeProducer (retryDataFamily a b tiles schedules) tile operand) < retryDataMemoryRank a b tiles schedules writer := by
    have h := hc.2.2
    change retryDataMemoryRank a b tiles schedules (retryNativeProducer (retryDataFamily a b tiles schedules) tile operand)+1 <
      retryDataMemoryRank a b tiles schedules writer+1 at h
    omega
  rcases retry_native_writer_phase (retryDataFamily a b tiles schedules)
    (retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb) (retry_data_complete a b tiles schedules ht hb)
    (retry_data_descriptors a b tiles schedules ht hb) hb hi hw with rfl | hold | hfuture
  · omega
  · have hback := retry_data_memory_byte_order_rank ht hb hold
    omega
  · exact retry_data_memory_byte_order_rank ht hb hfuture

theorem retry_data_memory_communication_rank {a b tiles schedules left right} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (he : Unified.Communication Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryDataReadWitness a b tiles schedules) (retryDataCoherenceWitness a b tiles schedules) left right) :
    retryDataMemoryRank a b tiles schedules left < retryDataMemoryRank a b tiles schedules right := by
  rcases he with ⟨loc,value,hr,hs,_⟩ | ⟨loc,hco⟩ | ⟨_,loc,value,hr,hco⟩
  · exact retry_data_memory_rf_rank ht hb hr hs
  · have h := hco.2.2
    change retryDataMemoryRank a b tiles schedules left+1 < retryDataMemoryRank a b tiles schedules right+1 at h
    omega
  · exact retry_data_memory_from_read_rank ht hb hr hco

theorem retry_data_sc_per_location (a b tiles schedules) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.SCPerLocation Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryDataReadWitness a b tiles schedules) (retryDataCoherenceWitness a b tiles schedules) := by
  intro members _ _ node _ hp
  have hh := hp.rank_lt (retryDataMemoryRank a b tiles schedules) (fun left right he =>
    he.2.2.elim (retry_data_memory_program_order_rank ht hb) (retry_data_memory_communication_rank ht hb))
  omega

end
end Ptx.Kernels.HopperDoubleBuffer
