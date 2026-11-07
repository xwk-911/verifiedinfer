import Ptx.Kernels.HopperDoubleBufferCoherentWitness

/-! Single-copy and RMW atomicity of the actual RF/co witness. Native reads
have one byte; other reads choose initial memory. No source operation both
reads and writes, as proved from the full source inventory. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_single_copy_atomicity (a b tiles) (hb : tiles ≤ 2^28) :
    Unified.SingleCopyAtomicity Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles) := by
  intro read writer _ loc vr vw hr hw hs other vr' vw' hr' hw'
  cases read with
  | base node => cases hs
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,he,hl,_⟩ := Unified.native_read_location hr
    obtain ⟨mark',call',he',hl',_⟩ := Unified.native_read_location hr'
    have hp := Option.some.inj (he.symm.trans he')
    cases hp
    have ho : other = loc := hl'.trans hl.symm
    subst other
    rw [hl] at hs
    rw [hs]
    exact (data_coherent_witness a b tiles hb).irrefl _ _

theorem data_read_node_no_write {a b tiles node loc value}
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) node loc = some value) :
    ∀ other, Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) node other = none := by
  intro other
  cases node with
  | wgmmaRead issue operand => exact Unified.native_write_none Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) issue operand other
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.readByte,Unified.kind,Access.kind,data_no_nonbulk] at hr
    | tma node =>
      cases node with
      | source event => rw [Unified.base_read_preserved,data_ordinary_read_none] at hr; cases hr
      | descriptor id => exact Access.descriptor_no_write Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view id other
      | read id offset => exact Access.tensor_read_no_write Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view id offset other
      | notify id => cases hr
      | write id offset =>
        cases hl : Tma.writeLocation Tma.localShared (dataCompleteCandidate a b tiles).view id offset <;>
          cases hv : Tma.transferByte (dataCompleteCandidate a b tiles).view id offset <;>
          simp [Unified.readByte,Unified.kind,Access.kind,hl,hv,Ptx.Event.Kind.readByte] at hr

theorem data_rmw_atomicity (a b tiles) :
    Unified.RMWAtomicity Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles)
      (dataReadWitness a b tiles) (dataCoherenceWitness a b tiles) := by
  intro atomic writer _ _ loc vr vw hr hw hco other va vb ha hb
  have hn := data_read_node_no_write hr other
  rw [ha] at hn
  cases hn

end
end Ptx.Kernels.HopperDoubleBuffer
