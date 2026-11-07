import Ptx.Hopper.ByteContentsFrames

/-! Values written by real checked events, and preservation by nonwriters.
These facts do not impose a global SC interpretation on weak PTX executions.
-/
namespace Ptx.Hopper.ByteContents
open Ptx.ISA Ptx.Hopper.Progress
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

theorem finish_writes_byte {block candidate histories node demands state next loc value}
    (hs : finish block candidate histories node demands state = .ok next)
    (hw : writeByte candidate node loc = some value) : valueAt next loc = some value := by
  have hm := ByteAuthority.Footprint.finish_spec (authority_finish_of_value_finish hs)
  have hf := finish_spec hs
  obtain ⟨demand,hd,he,_⟩ := hm.2.2.1 loc .write (hf.1.1.2 loc value hw)
  obtain ⟨old,hg⟩ := payload_of_held (hf.2.2.2.1 demand hd)
  have hx := finishCells_member (candidate := candidate) (node := node) hm.2.2.2.1 hd hg
  rw [he] at hx
  rw [hf.2.2.1]
  change (get? (finishCells candidate node demands state.cells) (ByteAuthority.key loc)).bind Payload.value = some value
  rw [hx,hw]
  rfl

theorem claim_preserves_value {block candidate histories request state next}
    (hs : claim block candidate histories request state = .ok next) (loc : Location) : valueAt next loc = valueAt state loc := by
  obtain ⟨old,hg,_,rfl,_⟩ := claim_spec hs
  by_cases he : ByteAuthority.key request.location = ByteAuthority.key loc
  · unfold valueAt claimed
    rw [get?_insert_eq he,← he,hg]
    rfl
  · unfold valueAt claimed
    rw [get?_insert_ne he]

theorem finish_preserves_unwritten {block candidate histories node demands state next loc}
    (hs : finish block candidate histories node demands state = .ok next)
    (hw : writeByte candidate node loc = none) : valueAt next loc = valueAt state loc := by
  have hm := ByteAuthority.Footprint.finish_spec (authority_finish_of_value_finish hs)
  have hf := finish_spec hs
  rw [hf.2.2.1]
  by_cases hk : ByteAuthority.key loc ∈ ByteAuthority.Footprint.keys demands
  · obtain ⟨demand,hd,he⟩ := List.mem_map.mp hk
    have hl : demand.location = loc := ByteAuthority.key_injective he
    obtain ⟨old,hg⟩ := payload_of_held (hf.2.2.2.1 demand hd)
    have hx := finishCells_member (candidate := candidate) (node := node) hm.2.2.2.1 hd hg
    rw [hl] at hx hg
    change (get? (finishCells candidate node demands state.cells) (ByteAuthority.key loc)).bind Payload.value = _
    rw [hx,hw,valueAt,hg]
    rfl
  · change (get? (finishCells candidate node demands state.cells) (ByteAuthority.key loc)).bind Payload.value = _
    rw [finishCells_outside _ _ _ _ _ hk]
    rfl

theorem finish_realizes_selected_write {block candidate histories writer demands state next loc value} {read : Unified.Node} {initial : Unified.ProxyMemory} {rf : Unified.ReadsFrom}
    (hs : finish block candidate histories writer demands state = .ok next)
    (hw : writeByte candidate writer loc = some value) (hrf : rf read loc = some writer) :
    valueAt next loc = Unified.sourceValue Tma.localShared Access.globalDescriptor candidate initial read loc (rf read loc) := by
  rw [hrf,Unified.sourceValue]
  exact (finish_writes_byte hs hw).trans hw.symm

theorem finishCells_held_original {candidate node demands cells k other mode}
    (hh : (get? (finishCells candidate node demands cells) k).map Payload.owner = some (.held other mode)) :
    (get? cells k).map Payload.owner = some (.held other mode) := by
  induction demands with
  | nil => exact hh
  | cons head rest ih =>
    unfold finishCells at hh
    cases hg : get? cells (ByteAuthority.key head.location) with
    | none => exact ih (by simpa only [hg] using hh)
    | some old =>
      rw [hg] at hh
      by_cases he : ByteAuthority.key head.location = k
      · rw [get?_insert_eq he] at hh
        cases hh
      · rw [get?_insert_ne he] at hh
        exact ih hh

theorem finish_preserves_empty_frame {block candidate histories node demands state next other}
    (hs : finish block candidate histories node demands state = .ok next)
    (hf : ByteAuthority.Footprint.Frame (erase state) other []) :
    ByteAuthority.Footprint.Frame (erase next) other [] := by
  intro k mode hg
  rw [(finish_spec hs).2.2.1] at hg
  change get? (Iris.Std.PartialMap.map Payload.owner (finishCells candidate node demands state.cells)) k = _ at hg
  rw [get?_map] at hg
  apply hf k mode
  change get? (Iris.Std.PartialMap.map Payload.owner state.cells) k = _
  rw [get?_map]
  exact finishCells_held_original hg

end
end Ptx.Hopper.ByteContents
