import Ptx.Kernels.HopperDoubleBufferMemoryRank

/-! Actual global reads are immutable; a read/write overlap must be a native
shared read. These source/region facts do not assume a causal memory witness
or globally unique shared writers. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem data_base_read_region {a b tiles node loc value} (hb : tiles ≤ 2^28)
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view node loc = some value) :
    loc.space = .global ∧ (loc.address < 4352 ∨ 65536 ≤ loc.address) := by
  cases node with
  | copyRead issue | copyWrite issue => simp [Access.readByte,Access.kind,data_no_nonbulk] at hr
  | tma node =>
    cases node with
    | source event => rw [data_ordinary_read_none] at hr; cases hr
    | notify id => cases hr
    | write id offset =>
      cases hl : Tma.writeLocation Tma.localShared (dataCompleteCandidate a b tiles).view id offset <;>
        cases hv : Tma.transferByte (dataCompleteCandidate a b tiles).view id offset <;>
        simp [Access.readByte,Access.kind,hl,hv,Ptx.Event.Kind.readByte] at hr
    | descriptor id =>
      cases hc : Tma.copyAt (dataCompleteCandidate a b tiles).view id with
      | none => simp [Access.readByte,Access.kind,hc] at hr
      | some op =>
        have hp : Ptx.Event.payloadByte (Access.globalDescriptor id.issue.thread op.descriptorAddress) (TensorMap.encode op.descriptor) loc = some value := by
          simpa only [Access.readByte,Access.kind,hc,Option.map_some,Option.bind_some,Ptx.Event.Kind.readByte] using hr
        have hbound := Ptx.Event.payloadByte_bounds hp
        rw [TensorMap.encode_length] at hbound
        refine ⟨hbound.1.symm,.inl ?_⟩
        obtain ⟨tile,ht,hcopy⟩ := data_all_source_copies a b tiles hb id op hc
        rcases hcopy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> dsimp [Access.globalDescriptor,dataCopyA,dataCopyB] at hbound <;> omega
    | read id offset =>
      have hl := Access.tensor_read_access (.inl (by rw [hr]; rfl))
      cases hc : Tma.copyAt (dataCompleteCandidate a b tiles).view id with
      | none => simp [Tma.readLocation,hc] at hl
      | some op =>
        have hs : Tma.sourceByte op.descriptor op.coordinates offset = some loc := by
          simpa only [Tma.readLocation,hc,Option.bind_some] using hl
        obtain ⟨_,_,hg,ha⟩ := Tma.source_byte_some hs
        refine ⟨hg,.inr ?_⟩
        obtain ⟨tile,ht,hcopy⟩ := data_all_source_copies a b tiles hb id op hc
        rcases hcopy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> dsimp [dataCopyA,dataCopyB,aView,bView,dataBBase] at ha <;> omega

theorem data_base_read_immutable {a b tiles node loc value} (hb : tiles ≤ 2^28)
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles).view node loc = some value) :
    ∀ writer, Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) writer loc = none := by
  obtain ⟨hg,ho⟩ := data_base_read_region hb hr
  intro writer
  cases hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) writer loc with
  | none => rfl
  | some observed =>
    obtain ⟨base,size,hf,hs | hout⟩ := data_write_footprint_regions hb hw
    all_goals have hbound := Unified.access_footprint_bounds (.inr (by rw [hw]; rfl)) hf
    · obtain ⟨hshared,_⟩ := hs
      have he := hshared.symm.trans (hbound.1.trans hg)
      cases he
    · obtain ⟨_,rfl,hlo,hhi,_⟩ := hout
      rcases ho with ho | ho <;> omega

theorem data_read_write_pair {a b tiles read writer loc vr vw} (hb : tiles ≤ 2^28)
    (hr : Unified.readByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) read loc = some vr)
    (hw : Unified.writeByte Tma.localShared Access.globalDescriptor (dataCompleteCandidate a b tiles) writer loc = some vw) :
    ∃ tile < tiles, ∃ operand, read = dataNativeRead a b tiles tile operand ∧ loc = dataNativeLocation a b tiles tile operand := by
  cases read with
  | base node => rw [data_base_read_immutable hb hr writer] at hw; cases hw
  | wgmmaRead issue operand =>
    obtain ⟨mark,call,he,hl,_⟩ := Unified.native_read_location hr
    obtain ⟨tile,ht,rfl,rfl⟩ := data_representative_call he
    exact ⟨tile,ht,operand,rfl,hl⟩

end
end Ptx.Kernels.HopperDoubleBuffer
