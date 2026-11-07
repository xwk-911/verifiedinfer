import Ptx.Hopper.ByteContents

/-! Extend a real successful value event with a disjoint available cell.
Its permission frame and unchanged read view are derived from the actual
source-use/footprint checks, rather than assumed for the extended state.
-/
namespace Ptx.Hopper.ByteContents
open Ptx.ISA Ptx.Hopper.Progress
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def withSpare (state : State) (loc : Location) (value : Option Symbolic.Byte) : State :=
  {state with cells := insert state.cells (ByteAuthority.key loc) ⟨.available,value⟩}

theorem erase_withSpare (state : State) (loc : Location) (value : Option Symbolic.Byte) :
    erase (withSpare state loc value) = {erase state with bytes := insert (erase state).bytes (ByteAuthority.key loc) .available} := by
  apply congrArg₂ ByteAuthority.State.mk
  · rfl
  · exact map_insert

theorem authority_finish_of_value_finish {block candidate histories node demands state next}
    (hs : finish block candidate histories node demands state = .ok next) :
    ByteAuthority.Footprint.finish block candidate histories (Unified.memoryControlNode node) demands (erase state) =
      .ok (ByteAuthority.retired (erase state) (Unified.memoryControlNode node)) := by
  unfold finish at hs
  cases ha : ByteAuthority.Footprint.finish block candidate histories (Unified.memoryControlNode node) demands (erase state) with
  | error error => simp [ha] at hs
  | ok authority => rw [← (ByteAuthority.Footprint.finish_spec ha).2.2.2.2.2.2]

theorem finish_withSpare {block candidate histories node demands state next loc value}
    (hs : finish block candidate histories node demands state = .ok next)
    (hn : ByteAuthority.key loc ∉ ByteAuthority.Footprint.keys demands) :
    finish block candidate histories node demands (withSpare state loc value) =
      .ok (finished candidate node demands (withSpare state loc value)) := by
  have hmeta := ByteAuthority.Footprint.finish_spec (authority_finish_of_value_finish hs)
  obtain ⟨hlinked,hreads,_,hheld,hframe,hready⟩ := finish_spec hs
  have hne : ∀ demand ∈ demands, ByteAuthority.key loc ≠ ByteAuthority.key demand.location := by
    intro demand hm he
    exact hn (List.mem_map.mpr ⟨demand,hm,he.symm⟩)
  have hheld' : ByteAuthority.Footprint.Held (erase (withSpare state loc value)) (Unified.memoryControlNode node) demands := by
    intro demand hm
    rw [erase_withSpare,get?_insert_ne (hne demand hm)]
    exact hheld demand hm
  have hframe' : ByteAuthority.Footprint.Frame (erase (withSpare state loc value)) (Unified.memoryControlNode node) demands := by
    intro k mode hg
    rw [erase_withSpare] at hg
    by_cases he : ByteAuthority.key loc = k
    · rw [get?_insert_eq he] at hg; cases hg
    · rw [get?_insert_ne he] at hg; exact hframe k mode hg
  have hreads' : Reads candidate node (withSpare state loc value) := by
    intro readLoc observed hr
    obtain ⟨demand,hm,he,_⟩ := hmeta.2.2.1 readLoc .read (hlinked.1.1 readLoc observed hr)
    have hk : ByteAuthority.key loc ≠ ByteAuthority.key readLoc := by
      intro h
      exact hn (List.mem_map.mpr ⟨demand,hm,(congrArg ByteAuthority.key he).trans h.symm⟩)
    change (get? (insert state.cells (ByteAuthority.key loc) ⟨.available,value⟩) (ByteAuthority.key readLoc)).bind Payload.value = some observed
    rw [get?_insert_ne hk]
    exact hreads readLoc observed hr
  apply finish_succeeds
  · exact ByteAuthority.Footprint.finish_succeeds hready hmeta.2.1 hmeta.2.2.1 hmeta.2.2.2.1 hheld' hframe'
  · exact hlinked
  · exact hreads'

theorem finished_spare_unchanged {candidate node demands state loc value}
    (hn : ByteAuthority.key loc ∉ ByteAuthority.Footprint.keys demands) :
    get? (finished candidate node demands (withSpare state loc value)).cells (ByteAuthority.key loc) = some ⟨.available,value⟩ := by
  change get? (finishCells candidate node demands (insert state.cells (ByteAuthority.key loc) ⟨.available,value⟩)) (ByteAuthority.key loc) = _
  rw [finishCells_outside _ _ _ _ _ hn]
  simp [get?_insert]

end
end Ptx.Hopper.ByteContents
