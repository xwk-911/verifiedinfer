import Ptx.Kernels.HopperDoubleBufferMemoryAtomicity

/-! Communication and per-location SC for the independently chosen RF/co.
RF, co and from-read edges all increase the checked memory rank; no SC or
already-admitted execution is a premise. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_memory_program_order_rank {a b tiles left right} (hb : tiles ≤ 2^28)
    (hp : Unified.ProgramOrder (dataCompleteCandidate a b tiles) left right) : dataMemoryRank tiles left < dataMemoryRank tiles right :=
  data_native_control_edge_rank hb (Unified.program_order_control_edge hp)

theorem data_memory_rf_rank {a b tiles read writer loc value} (hb : tiles ≤ 2^28)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) read loc = some value)
    (hs : dataReadWitness a b tiles read loc = some writer) : dataMemoryRank tiles writer < dataMemoryRank tiles read := by
  cases read with
  | base node => cases hs
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,he,hl,_⟩ := Unified.native_read_location hr
    obtain ⟨tile,ht,rfl,rfl⟩ := data_representative_call he
    subst loc
    change dataReadWitness a b tiles (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) = some writer at hs
    rw [data_read_witness_current a b tiles tile ht operand] at hs
    cases hs
    exact data_memory_byte_order_rank hb (data_native_byte_order a b tiles tile ht hb operand)

theorem data_memory_from_read_rank {a b tiles read writer loc value} (hb : tiles ≤ 2^28)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) read loc = some value)
    (hc : dataCoherenceWitness a b tiles loc (dataReadWitness a b tiles read loc) (some writer)) :
    dataMemoryRank tiles read < dataMemoryRank tiles writer := by
  obtain ⟨vw,hw⟩ := Option.isSome_iff_exists.mp hc.2.1
  obtain ⟨tile,ht,operand,rfl,rfl⟩ := data_read_write_pair hb hr hw
  rw [data_read_witness_current a b tiles tile ht operand] at hc
  have hco : dataMemoryRank tiles (dataNativeProducer a b tiles tile operand) < dataMemoryRank tiles writer := by
    have h := hc.2.2
    change dataMemoryRank tiles (dataNativeProducer a b tiles tile operand)+1 < dataMemoryRank tiles writer+1 at h
    omega
  rcases data_native_writer_phase ht hb hw with rfl | hold | hfuture
  · omega
  · have hback := data_memory_byte_order_rank hb hold
    omega
  · exact data_memory_byte_order_rank hb hfuture

theorem data_memory_communication_rank {a b tiles left right} (hb : tiles ≤ 2^28)
    (he : Unified.Communication Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles) left right) : dataMemoryRank tiles left < dataMemoryRank tiles right := by
  rcases he with ⟨loc,value,hr,hs,_⟩ | ⟨loc,hco⟩ | ⟨_,loc,value,hr,hco⟩
  · exact data_memory_rf_rank hb hr hs
  · have h := hco.2.2
    change dataMemoryRank tiles left+1 < dataMemoryRank tiles right+1 at h
    omega
  · exact data_memory_from_read_rank hb hr hco

theorem data_sc_per_location (a b tiles) (hb : tiles ≤ 2^28) :
    Unified.SCPerLocation Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles) := by
  intro members _ _ node _ hp
  have hh := hp.rank_lt (dataMemoryRank tiles) (fun left right he =>
    he.2.2.elim (data_memory_program_order_rank hb) (data_memory_communication_rank hb))
  omega

end
end Ptx.Kernels.HopperDoubleBuffer
