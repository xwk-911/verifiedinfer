import Ptx.Kernels.HopperDoubleBufferAccessRegions

/-! Actual footprint regions exclude mixed-size races for arbitrary RF.
Native eligibility no longer needs a caller-supplied no-race premise. RF
selection still explicitly requires full memory admission; this module does
not construct its independent RF/co/observer witness. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section

theorem data_no_mixed_size_race (a b tiles) (hb : tiles ≤ 2^28) (rf : Unified.ReadsFrom) :
    ¬Unified.MixedSizeRace Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster rf :=
  Unified.compatible_conflicts_no_mixed_size_race (fun _ _ _ _ => data_conflicting_footprints_equal hb)

theorem data_native_eligibility_derived (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (rf : Unified.ReadsFrom) (operand : Wgmma.OperandByte) :
    Unified.Eligible Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataHistories a b tiles) dataCluster rf (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) :=
  data_native_eligible ht hb (data_no_mixed_size_race a b tiles hb rf) operand

theorem data_native_rf_forced {a b tiles tile initial rf co} (ht : tile < tiles) (hb : tiles ≤ 2^28)
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      initial rf co (dataHistories a b tiles) dataCluster) (operand : Wgmma.OperandByte) :
    rf (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) =
      some (dataNativeProducer a b tiles tile operand) :=
  data_native_reads_from_current ht hb hc (data_no_mixed_size_race a b tiles hb rf) operand

theorem data_native_stale_rf_rejected {a b tiles tile old initial rf co} (ht : tile < tiles)
    (hold : old < tile) (hs : stage old = stage tile) (hb : tiles ≤ 2^28)
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      initial rf co (dataHistories a b tiles) dataCluster) (operand : Wgmma.OperandByte) :
    rf (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) ≠
      some (dataNativeProducer a b tiles old operand) :=
  data_native_stale_source_rejected ht hold hs hb hc (data_no_mixed_size_race a b tiles hb rf) operand

theorem data_native_future_rf_rejected {a b tiles tile next initial rf co} (hn : next < tiles)
    (hle : tile+2 ≤ next) (hs : stage next = stage tile) (hb : tiles ≤ 2^28)
    (hc : Unified.MemoryConditions Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      initial rf co (dataHistories a b tiles) dataCluster) (operand : Wgmma.OperandByte) :
    rf (dataNativeRead a b tiles tile operand) (dataNativeLocation a b tiles tile operand) ≠
      some (dataNativeProducer a b tiles next operand) :=
  data_native_future_source_rejected hn hle hs hb hc (data_no_mixed_size_race a b tiles hb rf) operand

end
end Ptx.Kernels.HopperDoubleBuffer
