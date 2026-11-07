import Ptx.Hopper.ByteOrder

/-! Recover actual byte-access locations and source kinds from the combined
inventory. These rules are independent of chosen payload values and rf/co. -/
namespace Ptx.Hopper.Access
open Ptx.ISA
noncomputable section

theorem access_kind {resolve descriptor c node loc} (ha : Accesses resolve descriptor c node loc) :
    ∃ k, kind resolve descriptor c node = some k := by
  cases hk : kind resolve descriptor c node with
  | none => simp [Accesses,readByte,writeByte,hk] at ha
  | some k => exact ⟨k,rfl⟩

theorem access_bounds {resolve descriptor c node loc base size}
    (ha : Accesses resolve descriptor c node loc)
    (hf : (kind resolve descriptor c node).bind Ptx.Event.Kind.footprint = some (base,size)) :
    base.space = loc.space ∧ base.address ≤ loc.address ∧ loc.address < base.address+size :=
  MemoryGraph.access_footprint_bounds (c := inventoryGraph resolve descriptor c) ha hf

theorem tensor_read_shape {resolve descriptor c id offset k}
    (hk : kind resolve descriptor c (.tma (.read id offset)) = some k) :
    ∃ loc value, Tma.readLocation c id offset = some loc ∧ Tma.transferByte c id offset = some value ∧ k = .read loc [value] := by
  simp only [kind,bind,Option.bind_eq_some_iff] at hk
  obtain ⟨loc,hl,value,hv,hk⟩ := hk
  exact ⟨loc,value,hl,hv,Option.some.inj hk.symm⟩

theorem tensor_write_shape {resolve descriptor c id offset k}
    (hk : kind resolve descriptor c (.tma (.write id offset)) = some k) :
    ∃ loc value, Tma.writeLocation resolve c id offset = some loc ∧ Tma.transferByte c id offset = some value ∧ k = .write loc [value] := by
  simp only [kind,bind,Option.bind_eq_some_iff] at hk
  obtain ⟨loc,hl,value,hv,hk⟩ := hk
  exact ⟨loc,value,hl,hv,Option.some.inj hk.symm⟩

theorem tensor_read_access {resolve descriptor c id offset loc}
    (ha : Accesses resolve descriptor c (.tma (.read id offset)) loc) : Tma.readLocation c id offset = some loc := by
  obtain ⟨k,hk⟩ := access_kind ha
  obtain ⟨actual,value,hl,_,rfl⟩ := tensor_read_shape hk
  have hb := access_bounds ha (show (kind resolve descriptor c _).bind Ptx.Event.Kind.footprint = some (actual,1) by simp [hk,Ptx.Event.Kind.footprint])
  have he : loc = actual := by
    rcases loc with ⟨space,address⟩
    rcases actual with ⟨aspace,aaddress⟩
    simp only at hb
    simp only [Location.mk.injEq]
    exact ⟨hb.1.symm,by omega⟩
  exact he ▸ hl

theorem tensor_write_access {resolve descriptor c id offset loc}
    (ha : Accesses resolve descriptor c (.tma (.write id offset)) loc) : Tma.writeLocation resolve c id offset = some loc := by
  obtain ⟨k,hk⟩ := access_kind ha
  obtain ⟨actual,value,hl,_,rfl⟩ := tensor_write_shape hk
  have hb := access_bounds ha (show (kind resolve descriptor c _).bind Ptx.Event.Kind.footprint = some (actual,1) by simp [hk,Ptx.Event.Kind.footprint])
  have he : loc = actual := by
    rcases loc with ⟨space,address⟩
    rcases actual with ⟨aspace,aaddress⟩
    simp only at hb
    simp only [Location.mk.injEq]
    exact ⟨hb.1.symm,by omega⟩
  exact he ▸ hl

end
end Ptx.Hopper.Access
