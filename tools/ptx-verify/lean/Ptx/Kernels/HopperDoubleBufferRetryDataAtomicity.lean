import Ptx.Kernels.HopperDoubleBufferRetryDataCoherent

/-! Atomicity for the actual retry RF/co witness: native reads are single
bytes, global reads select initialization, and source read nodes never write. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_data_single_copy_atomicity (a b tiles schedules) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.SingleCopyAtomicity Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryDataReadWitness a b tiles schedules) (retryDataCoherenceWitness a b tiles schedules) := by
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
    exact (retry_data_coherent_witness a b tiles schedules ht hb).irrefl _ _

theorem retry_data_read_node_no_write {a b tiles schedules node loc value} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) node loc = some value) :
    ∀ other, Unified.writeByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) node other = none := by
  intro other
  have hw := retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb
  have hc := retry_data_complete a b tiles schedules ht hb
  cases node with
  | wgmmaRead issue operand => exact Unified.native_write_none _ _ _ _ _ _
  | base node =>
    cases node with
    | copyRead issue | copyWrite issue => simp [Unified.readByte,Unified.kind,Access.kind,candidate_no_nonbulk hb hw hc] at hr
    | tma node =>
      cases node with
      | source event => rw [Unified.base_read_preserved,candidate_ordinary_read_none hb hw hc] at hr; cases hr
      | descriptor id => exact Access.descriptor_no_write Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules).view id other
      | read id offset => exact Access.tensor_read_no_write Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules).view id offset other
      | notify id => cases hr
      | write id offset =>
        cases hl : Tma.writeLocation Tma.localShared (retryDataCandidate a b tiles schedules).view id offset <;>
          cases hv : Tma.transferByte (retryDataCandidate a b tiles schedules).view id offset <;>
          simp [Unified.readByte,Unified.kind,Access.kind,hl,hv,Ptx.Event.Kind.readByte] at hr

theorem retry_data_rmw_atomicity (a b tiles schedules) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    Unified.RMWAtomicity Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules)
      (retryDataReadWitness a b tiles schedules) (retryDataCoherenceWitness a b tiles schedules) := by
  intro atomic writer _ _ loc vr vw hr hw hco other va vb ha hb'
  have hn := retry_data_read_node_no_write ht hb hr other
  rw [ha] at hn
  cases hn

end
end Ptx.Kernels.HopperDoubleBuffer
