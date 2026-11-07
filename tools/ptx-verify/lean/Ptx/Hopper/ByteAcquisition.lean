import Ptx.Hopper.ByteFootprint

/-! Actual sequential claim construction from available authority. All requests
check the unchanged source cut; grants cannot invent availability or source uses.
-/
namespace Ptx.Hopper.ByteAuthority.Footprint
open Ptx.ISA Ptx.Hopper.Progress
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def Available (state : State) (demands : List Demand) : Prop :=
  ∀ demand ∈ demands, get? state.bytes (key demand.location) = some .available

def granted : State → Unified.ControlNode → List Demand → State
  | state,_,[] => state
  | state,node,demand::rest => granted {state with bytes := insert state.bytes (key demand.location) (.held node demand.mode)} node rest

def pool : List Demand → HeapF Owner
  | [] => Iris.Std.PartialMap.empty
  | demand::rest => insert (pool rest) (key demand.location) .available

theorem pool_lookup (demands : List Demand) (k : Nat) :
    get? (pool demands) k = if k ∈ keys demands then some .available else none := by
  induction demands with
  | nil => rfl
  | cons demand rest ih =>
    by_cases he : key demand.location = k
    · simp [pool,keys,get?_insert,he]
    · simp [pool,keys,get?_insert_ne he,ih,Ne.symm he]

theorem pool_available (coupled : Bridge.State) (demands : List Demand) : Available ⟨coupled,pool demands⟩ demands := by
  intro demand hm
  change get? (pool demands) (key demand.location) = some .available
  have hk : key demand.location ∈ keys demands := List.mem_map.mpr ⟨demand,hm,rfl⟩
  rw [pool_lookup]
  simp only [hk,ite_true]

theorem pool_owners_available (demands : List Demand) (k : Nat) (owner : Owner)
    (hg : get? (pool demands) k = some owner) : owner = .available := by
  rw [pool_lookup] at hg
  split at hg
  · exact (Option.some.inj hg).symm
  · cases hg

def acquire (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (node : Unified.ControlNode) : List Demand → State → Except Error State
  | [],state => .ok state
  | demand::rest,state => (claim block candidate histories ⟨node,demand.location,demand.mode⟩ state).bind
      (fun next => acquire block candidate histories node rest next)

theorem granted_coupled (state : State) (node : Unified.ControlNode) (demands : List Demand) :
    (granted state node demands).coupled = state.coupled := by
  induction demands generalizing state with
  | nil => rfl
  | cons demand rest ih => exact ih _

theorem granted_outside (state : State) (node : Unified.ControlNode) (demands : List Demand) (k : Nat)
    (hn : k ∉ keys demands) : get? (granted state node demands).bytes k = get? state.bytes k := by
  induction demands generalizing state with
  | nil => rfl
  | cons demand rest ih =>
    have hh : key demand.location ≠ k := by intro he; exact hn (List.mem_cons.mpr (Or.inl he.symm))
    rw [granted,ih _ (by intro hm; exact hn (List.mem_cons.mpr (Or.inr hm)))]
    exact get?_insert_ne hh

theorem distinct_tail {head rest} (hd : Distinct (head::rest)) :
    key head.location ∉ keys rest ∧ Distinct rest := by
  simpa only [Distinct,keys,List.map_cons,List.nodup_cons] using hd

theorem available_after_head {state head rest node} (hd : Distinct (head::rest)) (ha : Available state (head::rest)) :
    Available {state with bytes := insert state.bytes (key head.location) (.held node head.mode)} rest := by
  intro demand hm
  have hn : key head.location ≠ key demand.location := by
    intro he; exact (distinct_tail hd).1 (List.mem_map.mpr ⟨demand,hm,he.symm⟩)
  rw [get?_insert_ne hn]
  exact ha demand (by simp [hm])

theorem granted_held (state : State) (node : Unified.ControlNode) (demands : List Demand) (hd : Distinct demands) :
    Held (granted state node demands) node demands := by
  induction demands generalizing state with
  | nil => intro demand hm; cases hm
  | cons head rest ih =>
    intro demand hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [granted,granted_outside _ _ _ _ (distinct_tail hd).1]
      simp [get?_insert]
    · exact ih _ (distinct_tail hd).2 demand hm

theorem acquire_succeeds {block candidate histories node state demands}
    (hr : Ready block candidate histories state.coupled.done node)
    (hs : Sound candidate node demands) (hd : Distinct demands) (ha : Available state demands) :
    acquire block candidate histories node demands state = .ok (granted state node demands) := by
  induction demands generalizing state with
  | nil => rfl
  | cons head rest ih =>
    have hhead : claim block candidate histories ⟨node,head.location,head.mode⟩ state =
        .ok {state with bytes := insert state.bytes (key head.location) (.held node head.mode)} :=
      claim_succeeds hr (hs head (by simp)) (ha head (by simp))
    simp only [acquire,hhead,Except.bind,granted]
    apply ih (state := {state with bytes := insert state.bytes (key head.location) (.held node head.mode)}) hr
      (by intro demand hm; exact hs demand (by simp [hm])) (distinct_tail hd).2
    exact available_after_head hd ha

theorem acquire_steps {block candidate histories cluster plan node demands state next}
    (hs : acquire block candidate histories node demands state = .ok next) :
    Steps block candidate histories cluster plan state next := by
  induction demands generalizing state with
  | nil => cases hs; exact .refl _
  | cons head rest ih =>
    unfold acquire at hs
    cases hh : claim block candidate histories ⟨node,head.location,head.mode⟩ state with
    | error error => simp [hh,Except.bind] at hs
    | ok mid =>
      exact .next (.claim hh) (ih (by simpa only [hh,Except.bind] using hs))

theorem acquire_requires_available {block candidate histories node demands state next}
    (hs : acquire block candidate histories node demands state = .ok next) : Available state demands := by
  induction demands generalizing state with
  | nil => intro demand hm; cases hm
  | cons head rest ih =>
    unfold acquire at hs
    cases hh : claim block candidate histories ⟨node,head.location,head.mode⟩ state with
    | error error => simp [hh,Except.bind] at hs
    | ok mid =>
      have ha := ih (by simpa only [hh,Except.bind] using hs)
      obtain ⟨_,_,havailable,rfl⟩ := claim_spec hh
      intro demand hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact havailable
      · have hmid := ha demand hm
        by_cases he : key head.location = key demand.location
        · simp only [get?_insert,he,ite_true] at hmid; cases hmid
        · simpa only [get?_insert_ne he] using hmid

theorem acquire_requires_distinct {block candidate histories node demands state next}
    (hs : acquire block candidate histories node demands state = .ok next) : Distinct demands := by
  induction demands generalizing state with
  | nil => simp [Distinct,keys]
  | cons head rest ih =>
    unfold acquire at hs
    cases hh : claim block candidate histories ⟨node,head.location,head.mode⟩ state with
    | error error => simp [hh,Except.bind] at hs
    | ok mid =>
      have hrest : acquire block candidate histories node rest mid = .ok next := by simpa only [hh,Except.bind] using hs
      have hd := ih hrest
      have ha := acquire_requires_available hrest
      have hn : key head.location ∉ keys rest := by
        intro hm
        obtain ⟨demand,hm,he⟩ := List.mem_map.mp hm
        have hl := ha demand hm
        rw [(claim_spec hh).2.2.2] at hl
        change get? (insert state.bytes (key head.location) (.held node head.mode)) (key demand.location) = some .available at hl
        simp [he,get?_insert] at hl
      simpa only [Distinct,keys,List.map_cons,List.nodup_cons] using And.intro hn hd

theorem granted_frame {block candidate histories node demands state}
    (hp : ∀ k owner, get? state.bytes k = some owner → owner = .available)
    (hr : Ready block candidate histories state.coupled.done node)
    (hs : Sound candidate node demands) (hc : Covers candidate node demands)
    (hd : Distinct demands) (ha : Available state demands) : Frame (granted state node demands) node demands := by
  have he := acquire_steps (cluster := fun _ _ => False) (plan := fun _ => none) (acquire_succeeds hr hs hd ha)
  exact frame_of_source (supported_steps (available_pool_supported hp) he)
    (steps_active (available_pool_active hp) he) hc

theorem clear_granted_restores (state : State) (node : Unified.ControlNode) (demands : List Demand)
    (hd : Distinct demands) (ha : Available state demands) : clear demands (granted state node demands).bytes = state.bytes := by
  apply equiv_iff_eq.mp
  intro k
  rw [clear_lookup]
  by_cases hm : k ∈ keys demands
  · obtain ⟨demand,hm',he⟩ := List.mem_map.mp hm
    rw [← he,ha demand hm']
    have hmem : key demand.location ∈ keys demands := List.mem_map.mpr ⟨demand,hm',rfl⟩
    simp only [hmem,ite_true]
  · simp only [hm,ite_false]
    exact granted_outside state node demands k hm

theorem finished_bytes_restore {block candidate histories node demands state}
    (hp : ∀ k owner, get? state.bytes k = some owner → owner = .available)
    (hr : Ready block candidate histories state.coupled.done node)
    (hs : Sound candidate node demands) (hc : Covers candidate node demands)
    (hd : Distinct demands) (ha : Available state demands) :
    (retired (granted state node demands) node).bytes = state.bytes := by
  have hf := granted_frame hp hr hs hc hd ha
  have hh := granted_held state node demands hd
  change Iris.Std.PartialMap.map (release node) (granted state node demands).bytes = state.bytes
  rw [← clear_eq_release hh hf]
  exact clear_granted_restores state node demands hd ha

theorem granted_frame_from_invariants {block candidate histories node demands state}
    (hp : Supported state) (hi : Active block candidate histories state)
    (hr : Ready block candidate histories state.coupled.done node)
    (hs : Sound candidate node demands) (hc : Covers candidate node demands)
    (hd : Distinct demands) (ha : Available state demands) : Frame (granted state node demands) node demands := by
  have he := acquire_steps (cluster := fun _ _ => False) (plan := fun _ => none) (acquire_succeeds hr hs hd ha)
  exact frame_of_source (supported_steps hp he) (steps_active hi he) hc

theorem finished_bytes_restore_from_invariants {block candidate histories node demands state}
    (hp : Supported state) (hi : Active block candidate histories state)
    (hr : Ready block candidate histories state.coupled.done node)
    (hs : Sound candidate node demands) (hc : Covers candidate node demands)
    (hd : Distinct demands) (ha : Available state demands) :
    (retired (granted state node demands) node).bytes = state.bytes := by
  change Iris.Std.PartialMap.map (release node) (granted state node demands).bytes = state.bytes
  rw [← clear_eq_release (granted_held state node demands hd) (granted_frame_from_invariants hp hi hr hs hc hd ha)]
  exact clear_granted_restores state node demands hd ha

def cycle (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (node : Unified.ControlNode) (demands : List Demand) (state : State) : Except Error State :=
  (acquire block candidate histories node demands state).bind (finish block candidate histories node demands)

theorem cycle_succeeds {block candidate histories node demands state}
    (hp : ∀ k owner, get? state.bytes k = some owner → owner = .available)
    (hr : Ready block candidate histories state.coupled.done node)
    (hs : Sound candidate node demands) (hc : Covers candidate node demands)
    (hd : Distinct demands) (ha : Available state demands) :
    cycle block candidate histories node demands state = .ok (retired (granted state node demands) node) := by
  have hready : Ready block candidate histories (granted state node demands).coupled.done node := by simpa only [granted_coupled] using hr
  simp only [cycle,acquire_succeeds hr hs hd ha,Except.bind]
  exact finish_succeeds hready hs hc hd (granted_held state node demands hd) (granted_frame hp hr hs hc hd ha)

theorem steps_trans {block candidate histories cluster plan state mid last}
    (ha : Steps block candidate histories cluster plan state mid) (hb : Steps block candidate histories cluster plan mid last) :
    Steps block candidate histories cluster plan state last := by
  induction ha with
  | refl => exact hb
  | next first rest ih => exact .next first (ih hb)

theorem cycle_steps {block candidate histories cluster plan node demands state next}
    (hs : cycle block candidate histories node demands state = .ok next) : Steps block candidate histories cluster plan state next := by
  unfold cycle at hs
  cases ha : acquire block candidate histories node demands state with
  | error error => simp [ha,Except.bind] at hs
  | ok mid =>
    have hf : finish block candidate histories node demands mid = .ok next := by simpa only [ha,Except.bind] using hs
    exact steps_trans (acquire_steps ha) (.next (finish_is_authority_step hf) (.refl _))

end
end Ptx.Hopper.ByteAuthority.Footprint
