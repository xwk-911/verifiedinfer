import Ptx.Hopper.UnifiedBytes

namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

theorem access_kind {resolve descriptor c node loc} (ha : Accesses resolve descriptor c node loc) :
    ∃ k, kind resolve descriptor c node = some k := by
  cases hk : kind resolve descriptor c node with
  | none => simp [Accesses,readByte,writeByte,hk] at ha
  | some k => exact ⟨k,rfl⟩
theorem access_footprint_exists {resolve descriptor c node loc} (ha : Accesses resolve descriptor c node loc) :
    ∃ base size, (kind resolve descriptor c node).bind Ptx.Event.Kind.footprint = some (base,size) := by
  obtain ⟨k,hk⟩ := access_kind ha
  cases k <;> simp_all [Accesses,readByte,writeByte,Ptx.Event.Kind.readByte,Ptx.Event.Kind.writeByte,Ptx.Event.Kind.footprint]
theorem access_footprint_bounds {resolve descriptor c node loc base size}
    (ha : Accesses resolve descriptor c node loc)
    (hf : (kind resolve descriptor c node).bind Ptx.Event.Kind.footprint = some (base,size)) :
    base.space = loc.space ∧ base.address ≤ loc.address ∧ loc.address < base.address+size :=
  MemoryGraph.access_footprint_bounds (c := inventoryGraph resolve descriptor c) ha hf

end
end Ptx.Hopper.Unified
