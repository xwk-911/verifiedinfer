import Ptx.Hopper.ByteInventory

/-! Lift an entire finite coupled source/protocol execution into checked byte
claims and retirements. The finite inventory bounds actual uses; each cycle
returns its bytes, so later availability is derived rather than assumed.
This serial authority witness does not assert GPU scheduling or race freedom.
-/
namespace Ptx.Hopper.ByteAuthority.Footprint
open Ptx.ISA Ptx.Hopper.Progress
noncomputable section

def Bounded (candidate : Unified.Candidate) (locations : List Location) : Prop :=
  ∀ node loc mode, Uses candidate node loc mode → loc ∈ locations

theorem inventory_cycle_endpoint {block candidate histories coupled node locations}
    (hb : ∀ loc mode, Uses candidate node loc mode → loc ∈ locations)
    (hr : Ready block candidate histories coupled.done node) :
    retired (granted (initialized coupled locations) node (inventory candidate node locations)) node =
      initialized {coupled with done := fun n => coupled.done n ∨ n = node} locations := by
  have hbytes := finished_bytes_restore (initialized_available coupled locations) hr
    (inventory_sound candidate node locations) (inventory_covers hb) (inventory_distinct candidate node locations)
    (inventory_available coupled candidate node locations)
  apply congrArg₂ State.mk
  · simp only [granted_coupled,initialized]
  · exact hbytes

theorem inventory_cycle_run {block candidate histories coupled node locations}
    (hb : ∀ loc mode, Uses candidate node loc mode → loc ∈ locations)
    (hr : Ready block candidate histories coupled.done node) :
    cycle block candidate histories node (inventory candidate node locations) (initialized coupled locations) =
      .ok (initialized {coupled with done := fun n => coupled.done n ∨ n = node} locations) := by
  rw [cycle_succeeds (initialized_available coupled locations) hr (inventory_sound candidate node locations)
    (inventory_covers hb) (inventory_distinct candidate node locations) (inventory_available coupled candidate node locations)]
  exact congrArg Except.ok (inventory_cycle_endpoint hb hr)

theorem lift_step {block candidate histories cluster plan before after locations}
    (hb : Bounded candidate locations)
    (hs : Bridge.Step block Tma.localShared candidate histories cluster plan before after) :
    Steps block candidate histories cluster plan (initialized before locations) (initialized after locations) := by
  cases hs with
  | access advance =>
    cases advance with
    | next node hp hf hpred =>
      exact cycle_steps (inventory_cycle_run (hb node) ⟨hp,hf,hpred⟩)
  | host action run => exact .next (.protocol (.host action run) rfl) (.refl _)
  | device stream run completion => exact .next (.protocol (.device stream run completion) rfl) (.refl _)

theorem lift_steps {block candidate histories cluster plan before after locations}
    (hb : Bounded candidate locations)
    (hs : Bridge.Steps block Tma.localShared candidate histories cluster plan before after) :
    Steps block candidate histories cluster plan (initialized before locations) (initialized after locations) := by
  induction hs with
  | refl => exact .refl _
  | next first rest ih => exact steps_trans (lift_step hb first) ih

theorem lift_prefix {block candidate histories cluster plan done locations}
    (hb : Bounded candidate locations) (protocol : Ptx.Async.State)
    (hr : Reached block candidate histories done) :
    Steps block candidate histories cluster plan
      (initialized ⟨protocol,fun _ => False⟩ locations) (initialized ⟨protocol,done⟩ locations) :=
  lift_steps hb (Bridge.prefix_execution protocol hr)

def regionLocations (region : Regions.Region) : List Location :=
  List.ofFn (fun offset : Fin region.bytes => region.base.add offset.val)

theorem mem_regionLocations {region : Regions.Region} {loc : Location} (hc : region.Contains loc) :
    loc ∈ regionLocations region := by
  obtain ⟨hs,hlo,hhi⟩ := hc
  let offset : Fin region.bytes := ⟨loc.address-region.base.address,by omega⟩
  apply List.mem_ofFn.mpr
  refine ⟨offset,?_⟩
  cases loc with
  | mk space address =>
    simp only [Location.add,Location.mk.injEq]
    refine ⟨hs.symm,?_⟩
    change region.base.address ≤ address at hlo
    change address < region.base.address+region.bytes at hhi
    change region.base.address+(address-region.base.address) = address
    omega

def bindingLocations (bindings : List Regions.Binding) : List Location :=
  bindings.flatMap (fun binding => regionLocations binding.region)

theorem bounded_of_bindings {candidate bindings}
    (hc : ∀ node loc mode, Uses candidate node loc mode → ∃ binding ∈ bindings, binding.region.Contains loc) :
    Bounded candidate (bindingLocations bindings) := by
  intro node loc mode hu
  obtain ⟨binding,hm,hr⟩ := hc node loc mode hu
  exact List.mem_flatMap.mpr ⟨binding,hm,mem_regionLocations hr⟩

/-- A list of actual source advances, with readiness at each successive cut. -/
inductive Ordered (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry) :
    Cut → List Unified.ControlNode → Cut → Prop
  | nil (done : Cut) : Ordered block candidate histories done [] done
  | cons {before after node rest} (ready : Ready block candidate histories before node)
      (tail : Ordered block candidate histories (fun n => before n ∨ n = node) rest after) :
      Ordered block candidate histories before (node::rest) after

theorem ordered_append {block candidate histories before mid after first last}
    (ha : Ordered block candidate histories before first mid) (hb : Ordered block candidate histories mid last after) :
    Ordered block candidate histories before (first ++ last) after := by
  induction ha with
  | nil => exact hb
  | cons hr tail ih => exact .cons hr (ih hb)

theorem reached_ordered {block candidate histories done} (hr : Reached block candidate histories done) :
    ∃ nodes, Ordered block candidate histories (fun _ => False) nodes done := by
  induction hr with
  | empty => exact ⟨[],.nil _⟩
  | next before advance ih =>
    obtain ⟨nodes,hn⟩ := ih
    cases advance with
    | next node hp hf hpred => exact ⟨nodes ++ [node],ordered_append hn (.cons ⟨hp,hf,hpred⟩ (.nil _))⟩

theorem ordered_fresh {block candidate histories before after nodes}
    (ho : Ordered block candidate histories before nodes after) : ∀ node ∈ nodes, ¬before node := by
  induction ho with
  | nil => intro node hm; cases hm
  | @cons before after head rest hr tail ih =>
    intro node hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hr.2.1
    · exact fun hd => ih node hm (Or.inl hd)

theorem ordered_nodup {block candidate histories before after nodes}
    (ho : Ordered block candidate histories before nodes after) : nodes.Nodup := by
  induction ho with
  | nil => exact List.nodup_nil
  | @cons before after node rest hr tail ih =>
    exact List.nodup_cons.mpr ⟨fun hm => ordered_fresh tail node hm (Or.inr rfl),ih⟩

theorem ordered_done {block candidate histories before after nodes}
    (ho : Ordered block candidate histories before nodes after) :
    ∀ node, after node ↔ before node ∨ node ∈ nodes := by
  induction ho with
  | nil => simp
  | @cons before after head rest hr tail ih =>
    intro node
    rw [ih]
    simp only [List.mem_cons]
    tauto

end
end Ptx.Hopper.ByteAuthority.Footprint
