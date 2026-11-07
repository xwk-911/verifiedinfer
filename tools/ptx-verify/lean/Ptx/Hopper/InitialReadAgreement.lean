import Ptx.Hopper.AccessInversion
import Ptx.Hopper.InputValues

/-! A constructor for an initial-memory read witness, independent of causal
admission. Descriptor bytes and transfer data retain their distinct proxies.
This rule supplies value agreement only; it does not grant visibility. -/
namespace Ptx.Hopper.Access
open Ptx.ISA
noncomputable section

theorem initial_read_value {resolve descriptor c} {initial : ProxyMemory}
    (hs : ∀ event loc, readByte resolve descriptor c (.tma (.source event)) loc = none)
    (hn : ∀ event, copyAt c event = none)
    (hd : ∀ id op, Tma.copyAt c id = some op →
      TensorMap.Stored (initial Tma.Proxy.tensormap) (descriptor id.issue.thread op.descriptorAddress) op.descriptor)
    (ht : ∀ id offset loc value, Tma.readLocation c id offset = some loc →
      Tma.transferByte c id offset = some value → value = initial Tma.Proxy.async loc)
    {read loc value} (hr : readByte resolve descriptor c read loc = some value) :
    initial read.proxy loc = value := by
  cases read with
  | copyRead issue | copyWrite issue => simp [readByte,kind,hn] at hr
  | tma node =>
    cases node with
    | source event => rw [hs] at hr; cases hr
    | notify id => cases hr
    | write id offset =>
      cases hl : Tma.writeLocation resolve c id offset <;> cases hv : Tma.transferByte c id offset <;>
        simp [readByte,kind,hl,hv,Ptx.Event.Kind.readByte] at hr
    | read id offset =>
      obtain ⟨k,hk⟩ := access_kind (.inl (by rw [hr]; rfl))
      obtain ⟨actual,observed,hl,hv,rfl⟩ := tensor_read_shape hk
      have hp : Ptx.Event.payloadByte actual [observed] loc = some value := by
        simpa only [readByte,hk,Option.bind_some,Ptx.Event.Kind.readByte] using hr
      obtain ⟨rfl,rfl⟩ := singleton_payload hp
      exact (ht id offset loc value hl hv).symm
    | descriptor id =>
      cases hc : Tma.copyAt c id with
      | none => simp [readByte,kind,hc] at hr
      | some op =>
        have hp : Ptx.Event.payloadByte (descriptor id.issue.thread op.descriptorAddress) (TensorMap.encode op.descriptor) loc = some value := by
          simpa only [readByte,kind,hc,Option.map_some,Option.bind_some,Ptx.Event.Kind.readByte] using hr
        have hb := Ptx.Event.payloadByte_bounds hp
        rw [TensorMap.encode_length] at hb
        let offset := loc.address-(descriptor id.issue.thread op.descriptorAddress).address
        have ho : offset < 128 := by dsimp [offset]; omega
        have hl : loc = (descriptor id.issue.thread op.descriptorAddress).add offset := by
          cases loc with
          | mk space address =>
            dsimp only at hb
            simp only [Location.add,Location.mk.injEq]
            exact ⟨hb.1.symm,by dsimp [offset]; omega⟩
        have hv := TensorMap.encoded_byte op.descriptor (descriptor id.issue.thread op.descriptorAddress) ho
        rw [hl] at hp
        have he := Option.some.inj (hp.symm.trans hv)
        rw [he,hl]
        exact hd id op hc offset ho

end
end Ptx.Hopper.Access
