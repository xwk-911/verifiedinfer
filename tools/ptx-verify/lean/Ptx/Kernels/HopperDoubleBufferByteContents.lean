import Ptx.Iris.ByteContentsPhases
import Ptx.Kernels.HopperDoubleBufferRetryMemoryInputs

/-! The double-buffer writer partition supplies the value script's phase rule.
The view theorem below requires an actual successful script and valid source
cut. `HopperDoubleBufferValueFrontier/ValueExecution` now construct a complete
source value script from the initial byte pool for the bounded positive-K data
family, including native arrivals. Public preparation, host/device protocol
composition with byte values, and runtime correspondence remain separate.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def byteContentsContext {tiles candidate} (family : ReplySourceFamily tiles candidate) : ByteContentsHeap.Context :=
  ⟨HopperStage.block,candidate,retryHistories family⟩

theorem retry_byte_contents_phase {tiles sourceInitial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (tile : Nat) (ht : tile < tiles) (operand : Wgmma.OperandByte) :
    ByteContentsHeap.PhaseOrder (byteContentsContext family)
      (retryNativeProducer family tile operand) (retryNativeRead family tile operand) (retryNativeLocation family tile operand) := by
  apply ByteContentsHeap.phase_of_byte_order (cluster := dataCluster) (candidate_no_nonbulk hb hw hc)
  intro writer value he
  exact retry_native_writer_phase family hw hc hd hb ht he

theorem retry_byte_contents_view_of_script {tiles sourceInitial candidate initial rf co} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles sourceInitial) candidate) (hc : Unified.Complete candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28)
    (hm : Unified.MemoryConditions Tma.localShared Access.globalDescriptor candidate initial rf co (retryHistories family) dataCluster)
    (tile : Nat) (ht : tile < tiles) (operand : Wgmma.OperandByte)
    (before written ready : ByteContents.State) (demands : List ByteAuthority.Footprint.Demand)
    (actions : List ByteContentsHeap.Action)
    (hv : Valid HopperStage.block candidate (retryHistories family) before.coupled.done)
    (hs : ByteContentsHeap.transition (byteContentsContext family) (.finish (retryNativeProducer family tile operand) demands) before = .ok written)
    (hr : IrisExecution.run (ByteContentsHeap.transition (byteContentsContext family)) actions written = .ok ready)
    (hp : ¬ready.coupled.done (Unified.memoryControlNode (retryNativeRead family tile operand))) :
    ByteContents.valueAt ready (retryNativeLocation family tile operand) = some ((family.calls tile 0).operandBytes operand.index) := by
  have hwrite := retry_native_current_write_value family hw hc hd hb hm tile ht operand
  have hrf := retry_native_reads_from_current family hw hc hd hb hm tile ht operand
  have hview := ByteContentsHeap.producer_to_reader_view (initial := initial) (byteContentsContext family) actions hv hs hwrite hr hp
    (retry_byte_contents_phase family hw hc hd hb tile ht operand) hrf
  rw [hrf,Unified.sourceValue] at hview
  exact hview.trans hwrite

end
end Ptx.Kernels.HopperDoubleBuffer
