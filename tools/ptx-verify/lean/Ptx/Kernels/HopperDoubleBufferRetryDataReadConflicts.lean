import Ptx.Kernels.HopperDoubleBufferRetryDataMemoryRank

/-! Actual base reads are immutable global inputs/maps. Any read/write byte
overlap is therefore an actual native shared operand, without a memory premise. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retry_data_base_read_region {a b tiles schedules node loc value} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules).view node loc = some value) :
    loc.space = .global ∧ (loc.address < 4352 ∨ 65536 ≤ loc.address) := by
  have hw := retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb
  have hc := retry_data_complete a b tiles schedules ht hb
  cases node with
  | copyRead issue | copyWrite issue => simp [Access.readByte,Access.kind,candidate_no_nonbulk hb hw hc] at hr
  | tma node =>
    cases node with
    | source event => rw [candidate_ordinary_read_none hb hw hc] at hr; cases hr
    | notify id => cases hr
    | write id offset =>
      cases hl : Tma.writeLocation Tma.localShared (retryDataCandidate a b tiles schedules).view id offset <;>
        cases hv : Tma.transferByte (retryDataCandidate a b tiles schedules).view id offset <;>
        simp [Access.readByte,Access.kind,hl,hv,Ptx.Event.Kind.readByte] at hr
    | descriptor id =>
      cases he : Tma.copyAt (retryDataCandidate a b tiles schedules).view id with
      | none => simp [Access.readByte,Access.kind,he] at hr
      | some op =>
        have hp : Ptx.Event.payloadByte (Access.globalDescriptor id.issue.thread op.descriptorAddress) (TensorMap.encode op.descriptor) loc = some value := by
          simpa only [Access.readByte,Access.kind,he,Option.map_some,Option.bind_some,Ptx.Event.Kind.readByte] using hr
        have hbound := Ptx.Event.payloadByte_bounds hp
        rw [TensorMap.encode_length] at hbound
        refine ⟨hbound.1.symm,.inl ?_⟩
        obtain ⟨tile,hi,ha | hb'⟩ := candidate_copy_geometry hb hw hc he
        · rw [ha.1] at hbound
          dsimp [Access.globalDescriptor] at hbound
          omega
        · rw [hb'.1] at hbound
          dsimp [Access.globalDescriptor] at hbound
          omega
    | read id offset =>
      have hl := Access.tensor_read_access (.inl (by rw [hr]; rfl))
      obtain ⟨hg,ha⟩ := candidate_tma_read_input_bounds hb hw hc (retry_data_descriptors a b tiles schedules ht hb) hl
      exact ⟨hg,.inr ha⟩

theorem retry_data_base_read_immutable {a b tiles schedules node loc value} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules).view node loc = some value) :
    ∀ writer, Unified.writeByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) writer loc = none := by
  obtain ⟨hg,ho⟩ := retry_data_base_read_region ht hb hr
  have hw := retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb
  have hc := retry_data_complete a b tiles schedules ht hb
  exact candidate_global_outside_output_immutable hb hw hc hg (by rcases ho with ho | ho <;> omega)

theorem retry_data_read_write_pair {a b tiles schedules read writer loc vr vw} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) read loc = some vr)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (retryDataCandidate a b tiles schedules) writer loc = some vw) :
    ∃ tile < tiles, ∃ operand, read = retryNativeRead (retryDataFamily a b tiles schedules) tile operand ∧
      loc = retryNativeLocation (retryDataFamily a b tiles schedules) tile operand := by
  cases read with
  | base node => rw [retry_data_base_read_immutable ht hb hr writer] at hw; cases hw
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,he,hl,_⟩ := Unified.native_read_location hr
    obtain ⟨tile,hi,rfl,rfl⟩ := retry_data_representative_call ht hb he
    exact ⟨tile,hi,operand,rfl,hl⟩

end
end Ptx.Kernels.HopperDoubleBuffer
