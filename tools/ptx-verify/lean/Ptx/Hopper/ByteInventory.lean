import Ptx.Hopper.ByteAcquisition

/-! Normalize finite actual-location inventories into source-sound footprints.
The inventory bounds are explicit; no membership or permission is invented.
Write grants dominate reads at an RMW byte. This is authority metadata only.
-/
namespace Ptx.Hopper.ByteAuthority.Footprint
open Ptx.ISA Ptx.Hopper.Progress
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

noncomputable def select (candidate : Unified.Candidate) (node : Unified.ControlNode) : List Location → List Demand
  | [] => []
  | loc::rest => by
    classical
    exact if Uses candidate node loc .write then ⟨loc,.write⟩::select candidate node rest
      else if Uses candidate node loc .read then ⟨loc,.read⟩::select candidate node rest
      else select candidate node rest

theorem select_sound (candidate : Unified.Candidate) (node : Unified.ControlNode) (locations : List Location) :
    Sound candidate node (select candidate node locations) := by
  induction locations with
  | nil => intro demand hm; cases hm
  | cons loc rest ih =>
    classical
    unfold select
    split
    · rename_i hw
      intro demand hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hw
      · exact ih demand hm
    · split
      · rename_i hr
        intro demand hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hr
        · exact ih demand hm
      · exact ih

theorem select_location {candidate node locations demand}
    (hm : demand ∈ select candidate node locations) : demand.location ∈ locations := by
  induction locations with
  | nil => cases hm
  | cons loc rest ih =>
    classical
    unfold select at hm
    split at hm
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hm)
    · split at hm
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih hm)
      · exact List.mem_cons_of_mem _ (ih hm)

theorem select_covers_member {candidate node locations loc mode}
    (hm : loc ∈ locations) (hu : Uses candidate node loc mode) :
    ∃ demand ∈ select candidate node locations, demand.location = loc ∧ Authorizes demand.mode mode := by
  induction locations with
  | nil => cases hm
  | cons head rest ih =>
    classical
    rcases List.mem_cons.mp hm with rfl | hm
    · unfold select
      split
      · exact ⟨⟨loc,.write⟩,List.mem_cons_self,rfl,write_authorizes _⟩
      · rename_i hn
        have hr : Uses candidate node loc .read := by cases mode with | read => exact hu | write => exact (hn hu).elim
        simp only [hr,ite_true]
        refine ⟨⟨loc,.read⟩,List.mem_cons_self,rfl,?_⟩
        cases mode with | read => exact authorizes_self _ | write => exact (hn hu).elim
    · obtain ⟨demand,hd,hl,ha⟩ := ih hm
      refine ⟨demand,?_,hl,ha⟩
      unfold select
      split
      · exact List.mem_cons_of_mem _ hd
      · split
        · exact List.mem_cons_of_mem _ hd
        · exact hd

theorem select_distinct {candidate node locations} (hn : locations.Nodup) : Distinct (select candidate node locations) := by
  induction locations with
  | nil => simp [select,Distinct,keys]
  | cons loc rest ih =>
    classical
    have hn' := List.nodup_cons.mp hn
    have hrest := ih hn'.2
    have hkey : key loc ∉ keys (select candidate node rest) := by
      intro hm
      obtain ⟨demand,hm,he⟩ := List.mem_map.mp hm
      have hl := key_injective he
      exact hn'.1 (hl ▸ select_location hm)
    unfold select
    split
    · simpa only [Distinct,keys,List.map_cons,List.nodup_cons] using And.intro hkey hrest
    · split
      · simpa only [Distinct,keys,List.map_cons,List.nodup_cons] using And.intro hkey hrest
      · exact hrest

noncomputable def inventory (candidate : Unified.Candidate) (node : Unified.ControlNode) (locations : List Location) : List Demand := by
  classical
  exact select candidate node locations.dedup

theorem inventory_sound (candidate : Unified.Candidate) (node : Unified.ControlNode) (locations : List Location) :
    Sound candidate node (inventory candidate node locations) := select_sound _ _ _

theorem inventory_distinct (candidate : Unified.Candidate) (node : Unified.ControlNode) (locations : List Location) :
    Distinct (inventory candidate node locations) := by
  classical
  exact select_distinct (List.nodup_dedup _)

theorem inventory_location {candidate node locations demand}
    (hm : demand ∈ inventory candidate node locations) : demand.location ∈ locations := by
  classical
  exact List.mem_dedup.mp (select_location hm)

theorem inventory_covers {candidate node locations}
    (hb : ∀ loc mode, Uses candidate node loc mode → loc ∈ locations) :
    Covers candidate node (inventory candidate node locations) := by
  classical
  intro loc mode hu
  exact select_covers_member (List.mem_dedup.mpr (hb loc mode hu)) hu

def locationDemands (locations : List Location) : List Demand := locations.map (fun loc => ⟨loc,.read⟩)
def initialized (coupled : Bridge.State) (locations : List Location) : State := ⟨coupled,pool (locationDemands locations)⟩

theorem initialized_available (coupled : Bridge.State) (locations : List Location) :
    ∀ k owner, get? (initialized coupled locations).bytes k = some owner → owner = .available := pool_owners_available _

theorem inventory_available (coupled : Bridge.State) (candidate : Unified.Candidate) (node : Unified.ControlNode) (locations : List Location) :
    Available (initialized coupled locations) (inventory candidate node locations) := by
  intro demand hm
  have hl := inventory_location hm
  change get? (pool (locationDemands locations)) (key demand.location) = some .available
  rw [pool_lookup]
  have hk : key demand.location ∈ keys (locationDemands locations) :=
    List.mem_map.mpr ⟨⟨demand.location,.read⟩,List.mem_map.mpr ⟨demand.location,hl,rfl⟩,rfl⟩
  simp only [hk,ite_true]

end
end Ptx.Hopper.ByteAuthority.Footprint
