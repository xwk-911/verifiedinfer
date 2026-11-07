import Ptx.Hopper.ByteAuthorityInvariant

/-! Complete finite access footprints. RMW may choose one write grant per byte;
exact source modes remain in Uses. Release frames all cells outside the list.
-/
namespace Ptx.Hopper.ByteAuthority.Footprint
open Ptx.ISA Ptx.Hopper.Progress
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

structure Demand where
  location : Location
  mode : Ptx.Async.Mode
  deriving Repr, DecidableEq

def keys (demands : List Demand) : List Nat := demands.map (fun demand => key demand.location)
def Distinct (demands : List Demand) : Prop := (keys demands).Nodup
def span (base : Location) (length : Nat) (mode : Ptx.Async.Mode) : List Demand :=
  List.ofFn (fun offset : Fin length => ⟨base.add offset.val,mode⟩)

theorem span_member (base : Location) (length : Nat) (mode : Ptx.Async.Mode) (offset : Fin length) :
    (⟨base.add offset.val,mode⟩ : Demand) ∈ span base length mode := List.mem_ofFn.mpr ⟨offset,rfl⟩

theorem span_distinct (base : Location) (length : Nat) (mode : Ptx.Async.Mode) : Distinct (span base length mode) := by
  simp only [Distinct,keys,span,List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right he
  have hl := key_injective he
  have ha := congrArg Location.address hl
  apply Fin.ext
  dsimp only [Location.add] at ha
  omega

def Sound (candidate : Unified.Candidate) (node : Unified.ControlNode) (demands : List Demand) : Prop :=
  ∀ demand ∈ demands, Uses candidate node demand.location demand.mode
def Covers (candidate : Unified.Candidate) (node : Unified.ControlNode) (demands : List Demand) : Prop :=
  ∀ loc mode, Uses candidate node loc mode → ∃ demand ∈ demands, demand.location = loc ∧ Authorizes demand.mode mode
def Held (state : State) (node : Unified.ControlNode) (demands : List Demand) : Prop :=
  ∀ demand ∈ demands, get? state.bytes (key demand.location) = some (.held node demand.mode)
def Frame (state : State) (node : Unified.ControlNode) (demands : List Demand) : Prop :=
  ∀ k mode, get? state.bytes k = some (.held node mode) → k ∈ keys demands

def Supported (state : State) : Prop := ∀ k node mode, get? state.bytes k = some (.held node mode) → ∃ loc, key loc = k

theorem supported_claim {block candidate histories request state next}
    (hi : Supported state) (hs : claim block candidate histories request state = .ok next) : Supported next := by
  rw [(claim_spec hs).2.2.2]
  intro k node mode hh
  by_cases he : key request.location = k
  · exact ⟨request.location,he⟩
  · exact hi k node mode (by simpa only [get?_insert_ne he] using hh)

theorem supported_retired {state node} (hi : Supported state) : Supported (retired state node) := by
  intro k control mode hh
  change get? (Iris.Std.PartialMap.map (release node) state.bytes) k = some (.held control mode) at hh
  rw [get?_map] at hh
  cases he : get? state.bytes k with
  | none => simp [he] at hh
  | some owner =>
    cases owner with
    | available => simp [he,release] at hh
    | held actual kind => exact hi k actual kind he

theorem supported_steps {block candidate histories cluster plan state next}
    (hi : Supported state) (hs : Steps block candidate histories cluster plan state next) : Supported next := by
  induction hs with
  | refl => exact hi
  | next first rest ih =>
    apply ih
    cases first with
    | claim hs => exact supported_claim hi hs
    | retire hr ha => exact supported_retired hi
    | protocol hs stable => exact hi

theorem available_pool_supported {state} (hp : ∀ k owner, get? state.bytes k = some owner → owner = .available) : Supported state := by
  intro k node mode hh
  have he := hp k _ hh
  cases he

theorem frame_of_source {block candidate histories state node demands} (hp : Supported state)
    (ha : Active block candidate histories state) (hc : Covers candidate node demands) : Frame state node demands := by
  intro k mode hh
  obtain ⟨loc,hl⟩ := hp k node mode hh
  obtain ⟨hu,_⟩ := ha loc node mode (by simpa only [hl] using hh)
  obtain ⟨demand,hm,he,_⟩ := hc loc mode hu
  exact List.mem_map.mpr ⟨demand,hm,by simpa only [he] using hl⟩

theorem all_held {candidate state node demands} (hc : Covers candidate node demands) (hh : Held state node demands) : AllHeld candidate state node := by
  intro loc mode hu
  obtain ⟨demand,hm,he,ha⟩ := hc loc mode hu
  exact ⟨demand.mode,by simpa only [he] using hh demand hm,ha⟩

def clear : List Demand → HeapF Owner → HeapF Owner
  | [],heap => heap
  | demand::rest,heap => insert (clear rest heap) (key demand.location) .available

theorem clear_lookup (demands : List Demand) (heap : HeapF Owner) (k : Nat) :
    get? (clear demands heap) k = if k ∈ keys demands then some .available else get? heap k := by
  induction demands with
  | nil => simp [clear,keys]
  | cons demand rest ih =>
    by_cases he : key demand.location = k
    · simp [clear,get?_insert,he,keys]
    · simp [clear,get?_insert_ne he,ih,keys,Ne.symm he]

theorem clear_eq_release {state node demands} (hh : Held state node demands) (hf : Frame state node demands) :
    clear demands state.bytes = Iris.Std.PartialMap.map (release node) state.bytes := by
  apply equiv_iff_eq.mp
  intro k
  rw [clear_lookup,get?_map]
  by_cases hm : k ∈ keys demands
  · obtain ⟨demand,hd,he⟩ := List.mem_map.mp hm
    rw [← he,hh demand hd]
    have hmem : key demand.location ∈ keys demands := List.mem_map.mpr ⟨demand,hd,rfl⟩
    simp [hmem,release]
  · simp only [hm,ite_false]
    cases he : get? state.bytes k with
    | none => rfl
    | some owner =>
      cases owner with
      | available => rfl
      | held actual mode =>
        have hn : actual ≠ node := by intro heq; subst actual; exact hm (hf k mode he)
        simp [release,hn]

def holding (node : Unified.ControlNode) : List Demand → HeapF Owner
  | [] => Iris.Std.PartialMap.empty
  | demand::rest => insert (holding node rest) (key demand.location) (.held node demand.mode)

theorem holding_held (node : Unified.ControlNode) (demands : List Demand) (hd : Distinct demands) :
    ∀ demand ∈ demands, get? (holding node demands) (key demand.location) = some (.held node demand.mode) := by
  induction demands with
  | nil => simp
  | cons head rest ih =>
    have hdistinct : key head.location ∉ keys rest ∧ Distinct rest := by
      simpa only [Distinct,keys,List.map_cons,List.nodup_cons] using hd
    intro demand hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [holding,get?_insert]
    · have hne : key head.location ≠ key demand.location := by
        intro he
        exact hdistinct.1 (List.mem_map.mpr ⟨demand,hm,he.symm⟩)
      simpa only [holding,get?_insert_ne hne] using ih hdistinct.2 demand hm

theorem holding_frame (node : Unified.ControlNode) (demands : List Demand) (k : Nat) (mode : Ptx.Async.Mode) :
    get? (holding node demands) k = some (.held node mode) → k ∈ keys demands := by
  induction demands with
  | nil => intro h; cases h
  | cons head rest ih =>
    intro h
    by_cases he : key head.location = k
    · exact List.mem_cons.mpr (Or.inl he.symm)
    · have hr : get? (holding node rest) k = some (.held node mode) := by simpa only [holding,get?_insert_ne he] using h
      exact List.mem_cons.mpr (Or.inr (ih hr))

noncomputable def finish (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (node : Unified.ControlNode) (demands : List Demand) (state : State) : Except Error State := by
  classical
  exact if Ready block candidate histories state.coupled.done node then
    if Sound candidate node demands ∧ Covers candidate node demands ∧ Distinct demands ∧ Held state node demands ∧ Frame state node demands then
      .ok (retired state node)
    else .error .unavailable
  else .error .unready

theorem finish_succeeds {block candidate histories node demands state}
    (hr : Ready block candidate histories state.coupled.done node) (hs : Sound candidate node demands)
    (hc : Covers candidate node demands) (hd : Distinct demands) (hh : Held state node demands) (hf : Frame state node demands) :
    finish block candidate histories node demands state = .ok (retired state node) := by simp [finish,hr,hs,hc,hd,hh,hf]

theorem finish_spec {block candidate histories node demands state next}
    (hs : finish block candidate histories node demands state = .ok next) :
    Ready block candidate histories state.coupled.done node ∧ Sound candidate node demands ∧ Covers candidate node demands ∧
      Distinct demands ∧ Held state node demands ∧ Frame state node demands ∧ next = retired state node := by
  unfold finish at hs
  split at hs
  · rename_i hr
    split at hs
    · rename_i h
      exact ⟨hr,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,Except.ok.inj hs.symm⟩
    · cases hs
  · cases hs

theorem finish_is_authority_step {block candidate histories cluster plan node demands state next}
    (hs : finish block candidate histories node demands state = .ok next) : Step block candidate histories cluster plan state next := by
  obtain ⟨hr,_,hc,_,hh,_,rfl⟩ := finish_spec hs
  exact .retire hr (all_held hc hh)

end
end Ptx.Hopper.ByteAuthority.Footprint
