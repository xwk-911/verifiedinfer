import Ptx.Hopper.ByteAcquisition
import Ptx.Hopper.UnifiedVisibility

/-! Event-local byte contents coupled to the existing access authority.
Values come from actual emitted writes; all emitted reads are checked before
the atomic event update. A realization of RF in this local view is explicit:
an arbitrary weak-memory execution is not assumed to be one SC heap history.
-/
namespace Ptx.Hopper.ByteContents
open Ptx.ISA Ptx.Hopper.Progress
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

abbrev HeapF := ByteAuthority.HeapF
abbrev Demand := ByteAuthority.Footprint.Demand
structure Payload where
  owner : ByteAuthority.Owner
  value : Option Symbolic.Byte
structure State where
  coupled : Bridge.State
  cells : HeapF Payload

def erase (state : State) : ByteAuthority.State := ⟨state.coupled,Iris.Std.PartialMap.map Payload.owner state.cells⟩
def valueAt (state : State) (loc : Location) : Option Symbolic.Byte := (get? state.cells (ByteAuthority.key loc)).bind Payload.value
def readByte (candidate : Unified.Candidate) (node : Unified.Node) (loc : Location) :=
  Unified.readByte Tma.localShared Access.globalDescriptor candidate node loc
def writeByte (candidate : Unified.Candidate) (node : Unified.Node) (loc : Location) :=
  Unified.writeByte Tma.localShared Access.globalDescriptor candidate node loc
def CompleteAt (candidate : Unified.Candidate) (node : Unified.Node) : Prop :=
  ∀ other, Unified.memoryControlNode other = Unified.memoryControlNode node →
    (∃ loc value, readByte candidate other loc = some value ∨ writeByte candidate other loc = some value) → other = node

def Linked (candidate : Unified.Candidate) (node : Unified.Node) : Prop :=
  ((∀ loc value, readByte candidate node loc = some value → ByteAuthority.Uses candidate (Unified.memoryControlNode node) loc .read) ∧
  (∀ loc value, writeByte candidate node loc = some value → ByteAuthority.Uses candidate (Unified.memoryControlNode node) loc .write)) ∧
    CompleteAt candidate node
def Reads (candidate : Unified.Candidate) (node : Unified.Node) (state : State) : Prop :=
  ∀ loc value, readByte candidate node loc = some value → valueAt state loc = some value

def RealizesRF (candidate : Unified.Candidate) (initial : Unified.ProxyMemory) (rf : Unified.ReadsFrom)
    (node : Unified.Node) (state : State) : Prop :=
  ∀ loc value, readByte candidate node loc = some value →
    valueAt state loc = Unified.sourceValue Tma.localShared Access.globalDescriptor candidate initial node loc (rf node loc)

theorem reads_from_agreement {candidate initial rf node state histories cluster co}
    (ha : Unified.CausalConstraints Tma.localShared Access.globalDescriptor candidate initial rf co histories cluster)
    (he : ∀ loc value, readByte candidate node loc = some value →
      Unified.Eligible Tma.localShared Access.globalDescriptor candidate histories cluster rf node loc)
    (hs : RealizesRF candidate initial rf node state) : Reads candidate node state := by
  intro loc value hr
  exact (hs loc value hr).trans (ha.agreement node loc value (he loc value hr) hr)

def finishCells (candidate : Unified.Candidate) (node : Unified.Node) : List Demand → HeapF Payload → HeapF Payload
  | [],cells => cells
  | demand::rest,cells => match get? cells (ByteAuthority.key demand.location) with
    | none => finishCells candidate node rest cells
    | some old => insert (finishCells candidate node rest cells) (ByteAuthority.key demand.location)
        ⟨.available,(writeByte candidate node demand.location).or old.value⟩

def finished (candidate : Unified.Candidate) (node : Unified.Node) (demands : List Demand) (state : State) : State :=
  ⟨⟨state.coupled.protocol,fun n => state.coupled.done n ∨ n = Unified.memoryControlNode node⟩,
    finishCells candidate node demands state.cells⟩

inductive Error
  | authority (error : ByteAuthority.Error)
  | unlinked | readMismatch | memoryControl
  | preparationClosed | preparationNotReady | unprepared

noncomputable def finish (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (node : Unified.Node) (demands : List Demand) (state : State) : Except Error State := by
  classical
  exact match ByteAuthority.Footprint.finish block candidate histories (Unified.memoryControlNode node) demands (erase state) with
    | .error error => .error (.authority error)
    | .ok _ => if Linked candidate node then
        if Reads candidate node state then .ok (finished candidate node demands state) else .error .readMismatch
      else .error .unlinked

theorem payload_of_held {state : State} {loc node mode}
    (hh : get? (erase state).bytes (ByteAuthority.key loc) = some (.held node mode)) :
    ∃ value, get? state.cells (ByteAuthority.key loc) = some ⟨.held node mode,value⟩ := by
  change get? (Iris.Std.PartialMap.map Payload.owner state.cells) (ByteAuthority.key loc) = some (.held node mode) at hh
  rw [get?_map] at hh
  cases hg : get? state.cells (ByteAuthority.key loc) with
  | none => simp [hg] at hh
  | some payload =>
    have he : payload.owner = .held node mode := by simpa only [hg,Option.map_some,Option.some.injEq] using hh
    cases payload
    cases he
    exact ⟨_,rfl⟩

theorem finishCells_erase {candidate node demands state}
    (hh : ByteAuthority.Footprint.Held (erase state) (Unified.memoryControlNode node) demands) :
    Iris.Std.PartialMap.map Payload.owner (finishCells candidate node demands state.cells) =
      ByteAuthority.Footprint.clear demands (erase state).bytes := by
  induction demands with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨value,hg⟩ := payload_of_held (hh head (by simp))
    have ht : ByteAuthority.Footprint.Held (erase state) (Unified.memoryControlNode node) rest := by
      intro demand hm; exact hh demand (by simp [hm])
    simp only [finishCells,hg,ByteAuthority.Footprint.clear,map_insert,ih ht]

theorem erase_finished {candidate node demands state}
    (hh : ByteAuthority.Footprint.Held (erase state) (Unified.memoryControlNode node) demands)
    (hf : ByteAuthority.Footprint.Frame (erase state) (Unified.memoryControlNode node) demands) :
    erase (finished candidate node demands state) = ByteAuthority.retired (erase state) (Unified.memoryControlNode node) := by
  apply congrArg₂ ByteAuthority.State.mk
  · rfl
  · change Iris.Std.PartialMap.map Payload.owner (finishCells candidate node demands state.cells) = _
    rw [finishCells_erase hh,ByteAuthority.Footprint.clear_eq_release hh hf]

theorem finish_succeeds {block candidate histories node demands state}
    (ha : ByteAuthority.Footprint.finish block candidate histories (Unified.memoryControlNode node) demands (erase state) =
      .ok (ByteAuthority.retired (erase state) (Unified.memoryControlNode node)))
    (hl : Linked candidate node) (hr : Reads candidate node state) :
    finish block candidate histories node demands state = .ok (finished candidate node demands state) := by
  simp only [finish,ha,hl,hr,ite_true]

theorem finish_read_mismatch {block candidate histories node demands state}
    (ha : ByteAuthority.Footprint.finish block candidate histories (Unified.memoryControlNode node) demands (erase state) =
      .ok (ByteAuthority.retired (erase state) (Unified.memoryControlNode node)))
    (hl : Linked candidate node) (hr : ¬Reads candidate node state) :
    finish block candidate histories node demands state = .error .readMismatch := by
  simp only [finish,ha,hl,hr,ite_true,ite_false]

theorem finish_spec {block candidate histories node demands state next}
    (hs : finish block candidate histories node demands state = .ok next) :
    Linked candidate node ∧ Reads candidate node state ∧ next = finished candidate node demands state ∧
      ByteAuthority.Footprint.Held (erase state) (Unified.memoryControlNode node) demands ∧
      ByteAuthority.Footprint.Frame (erase state) (Unified.memoryControlNode node) demands ∧
      ByteAuthority.Ready block candidate histories state.coupled.done (Unified.memoryControlNode node) := by
  unfold finish at hs
  cases ha : ByteAuthority.Footprint.finish block candidate histories (Unified.memoryControlNode node) demands (erase state) with
  | error error => simp [ha] at hs
  | ok authority =>
    simp only [ha] at hs
    split at hs
    · rename_i hl
      split at hs
      · rename_i hr
        have hf := ByteAuthority.Footprint.finish_spec ha
        exact ⟨hl,hr,(Except.ok.inj hs).symm,hf.2.2.2.2.1,hf.2.2.2.2.2.1,hf.1⟩
      · cases hs
    · cases hs

theorem finish_projects {block candidate histories cluster plan node demands state next}
    (hs : finish block candidate histories node demands state = .ok next) :
    ByteAuthority.Step block candidate histories cluster plan (erase state) (erase next) := by
  obtain ⟨_,_,rfl,hh,hf,hr⟩ := finish_spec hs
  rw [erase_finished hh hf]
  have ha : ByteAuthority.AllHeld candidate (erase state) (Unified.memoryControlNode node) := by
    unfold finish at hs
    cases he : ByteAuthority.Footprint.finish block candidate histories (Unified.memoryControlNode node) demands (erase state) with
    | error error => simp [he] at hs
    | ok value => exact ByteAuthority.Footprint.all_held (ByteAuthority.Footprint.finish_spec he).2.2.1 hh
  exact .retire hr ha

theorem finishCells_outside (candidate : Unified.Candidate) (node : Unified.Node) (demands : List Demand) (cells : HeapF Payload)
    (k : Nat) (hn : k ∉ ByteAuthority.Footprint.keys demands) :
    get? (finishCells candidate node demands cells) k = get? cells k := by
  induction demands with
  | nil => rfl
  | cons head rest ih =>
    have ht : k ∉ ByteAuthority.Footprint.keys rest := by intro hm; exact hn (List.mem_cons_of_mem _ hm)
    have hne : ByteAuthority.key head.location ≠ k := by intro he; exact hn (by simp [ByteAuthority.Footprint.keys,he])
    unfold finishCells
    cases hg : get? cells (ByteAuthority.key head.location) with
    | none => exact ih ht
    | some old => rw [get?_insert_ne hne]; exact ih ht

theorem finishCells_member {candidate node demands cells demand old}
    (hd : ByteAuthority.Footprint.Distinct demands) (hm : demand ∈ demands)
    (hg : get? cells (ByteAuthority.key demand.location) = some old) :
    get? (finishCells candidate node demands cells) (ByteAuthority.key demand.location) =
      some ⟨.available,(writeByte candidate node demand.location).or old.value⟩ := by
  induction demands with
  | nil => cases hm
  | cons head rest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [finishCells,hg,get?_insert]
      rfl
    · have ht := ByteAuthority.Footprint.distinct_tail hd
      have hne : ByteAuthority.key head.location ≠ ByteAuthority.key demand.location := by
        intro he; exact ht.1 (List.mem_map.mpr ⟨demand,hm,he.symm⟩)
      unfold finishCells
      cases hh : get? cells (ByteAuthority.key head.location) with
      | none => exact ih ht.2 hm
      | some value => rw [get?_insert_ne hne]; exact ih ht.2 hm

def claimed (state : State) (request : ByteAuthority.Claim) (old : Payload) : State :=
  {state with cells := insert state.cells (ByteAuthority.key request.location) ⟨.held request.node request.mode,old.value⟩}

noncomputable def claim (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (request : ByteAuthority.Claim) (state : State) : Except Error State :=
  match ByteAuthority.claim block candidate histories request (erase state) with
  | .error error => .error (.authority error)
  | .ok _ => match get? state.cells (ByteAuthority.key request.location) with
    | none => .error (.authority .unavailable)
    | some old => .ok (claimed state request old)

theorem erase_claimed (state : State) (request : ByteAuthority.Claim) (old : Payload) :
    erase (claimed state request old) = {erase state with bytes := insert (erase state).bytes (ByteAuthority.key request.location) (.held request.node request.mode)} := by
  apply congrArg₂ ByteAuthority.State.mk
  · rfl
  · exact map_insert

theorem claim_succeeds {block candidate histories request state value}
    (hr : ByteAuthority.Ready block candidate histories state.coupled.done request.node)
    (hu : ByteAuthority.Uses candidate request.node request.location request.mode)
    (hg : get? state.cells (ByteAuthority.key request.location) = some ⟨.available,value⟩) :
    claim block candidate histories request state = .ok (claimed state request ⟨.available,value⟩) := by
  have ha : get? (erase state).bytes (ByteAuthority.key request.location) = some .available := by
    change get? (Iris.Std.PartialMap.map Payload.owner state.cells) (ByteAuthority.key request.location) = some .available
    rw [get?_map,hg]; rfl
  simp only [claim,ByteAuthority.claim_succeeds hr hu ha,hg]

theorem claim_unready {block candidate histories request state}
    (hr : ¬ByteAuthority.Ready block candidate histories state.coupled.done request.node) :
    claim block candidate histories request state = .error (.authority .unready) := by
  simp only [claim,ByteAuthority.claim,erase,hr,ite_false]

theorem claim_spec {block candidate histories request state next}
    (hs : claim block candidate histories request state = .ok next) :
    ∃ old, get? state.cells (ByteAuthority.key request.location) = some old ∧ old.owner = .available ∧
      next = claimed state request old ∧
      ByteAuthority.claim block candidate histories request (erase state) = .ok (erase next) := by
  unfold claim at hs
  cases ha : ByteAuthority.claim block candidate histories request (erase state) with
  | error error => simp [ha] at hs
  | ok authority =>
    cases hg : get? state.cells (ByteAuthority.key request.location) with
    | none => simp [ha,hg] at hs
    | some old =>
      have he : next = claimed state request old := (Except.ok.inj (by simpa only [ha,hg] using hs)).symm
      have hp := ByteAuthority.claim_spec ha
      have ho : old.owner = .available := by
        have hx := hp.2.2.1
        change get? (Iris.Std.PartialMap.map Payload.owner state.cells) (ByteAuthority.key request.location) = some .available at hx
        simpa only [get?_map,hg,Option.map_some,Option.some.injEq] using hx
      refine ⟨old,rfl,ho,he,?_⟩
      rw [he,erase_claimed,← hp.2.2.2]

def initialCells (locations : List Location) (initial : Location → Symbolic.Byte) : HeapF Payload :=
  locations.foldr (fun loc rest => insert rest (ByteAuthority.key loc) ⟨.available,some (initial loc)⟩) Iris.Std.PartialMap.empty

theorem initialCells_member {locations initial loc} (hm : loc ∈ locations) :
    get? (initialCells locations initial) (ByteAuthority.key loc) = some ⟨.available,some (initial loc)⟩ := by
  induction locations with
  | nil => cases hm
  | cons head rest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [initialCells,get?_insert]
    · by_cases he : head = loc
      · subst head; simp [initialCells,get?_insert]
      · have hk : ByteAuthority.key head ≠ ByteAuthority.key loc := fun h => he (ByteAuthority.key_injective h)
        change get? (insert (initialCells rest initial) (ByteAuthority.key head) _) (ByteAuthority.key loc) = _
        rw [get?_insert_ne hk]
        exact ih hm

theorem dom_insert_present {cells : HeapF Payload} {k old fresh}
    (hg : get? cells k = some old) : dom (insert cells k fresh) = dom cells := by
  funext other
  by_cases he : k = other
  · subst other; simp [dom,get?_insert,hg]
  · simp [dom,get?_insert_ne he]

theorem finishCells_domain (candidate : Unified.Candidate) (node : Unified.Node) (demands : List Demand) (cells : HeapF Payload) :
    dom (finishCells candidate node demands cells) = dom cells := by
  induction demands with
  | nil => rfl
  | cons head rest ih =>
    unfold finishCells
    cases hg : get? cells (ByteAuthority.key head.location) with
    | none => exact ih
    | some old =>
      funext k
      by_cases he : ByteAuthority.key head.location = k
      · subst k; simp [dom,get?_insert,hg]
      · simpa only [dom,get?_insert_ne he] using congrFun ih k

theorem claim_domain {block candidate histories request state next}
    (hs : claim block candidate histories request state = .ok next) : dom next.cells = dom state.cells := by
  obtain ⟨old,hg,_,rfl,_⟩ := claim_spec hs
  exact dom_insert_present hg

theorem finish_domain {block candidate histories node demands state next}
    (hs : finish block candidate histories node demands state = .ok next) : dom next.cells = dom state.cells := by
  rw [(finish_spec hs).2.2.1]
  exact finishCells_domain _ _ _ _

theorem initialCells_owner_available {locations initial k payload}
    (hg : get? (initialCells locations initial) k = some payload) : payload.owner = .available := by
  induction locations with
  | nil =>
    change (none : Option Payload) = some payload at hg
    cases hg
  | cons head rest ih =>
    change get? (insert (initialCells rest initial) (ByteAuthority.key head) _) k = some payload at hg
    by_cases he : ByteAuthority.key head = k
    · rw [get?_insert_eq he] at hg
      cases hg
      rfl
    · rw [get?_insert_ne he] at hg
      exact ih hg

def withValue (state : State) (loc : Location) (value : Option Symbolic.Byte) : State :=
  match get? state.cells (ByteAuthority.key loc) with
  | none => state
  | some old => {state with cells := insert state.cells (ByteAuthority.key loc) ⟨old.owner,value⟩}

theorem withValue_coupled (state : State) (loc : Location) (value : Option Symbolic.Byte) :
    (withValue state loc value).coupled = state.coupled := by
  unfold withValue
  cases get? state.cells (ByteAuthority.key loc) <;> rfl

theorem erase_withValue (state : State) (loc : Location) (value : Option Symbolic.Byte) :
    erase (withValue state loc value) = erase state := by
  unfold withValue
  cases hg : get? state.cells (ByteAuthority.key loc) with
  | none => rfl
  | some old =>
    apply congrArg₂ ByteAuthority.State.mk
    · rfl
    · change Iris.Std.PartialMap.map Payload.owner (insert state.cells (ByteAuthority.key loc) _) = _
      rw [map_insert]
      apply equiv_iff_eq.mp
      intro k
      by_cases he : ByteAuthority.key loc = k
      · subst k
        simp only [get?_insert,get?_map,hg,ite_true,Option.map_some]
      · simp only [get?_insert_ne he]

theorem withValue_lookup {state loc old value}
    (hg : get? state.cells (ByteAuthority.key loc) = some old) :
    valueAt (withValue state loc value) loc = value := by
  simp only [withValue,hg,valueAt,get?_insert]
  rfl

theorem ordinary_complete_at {candidate id kind}
    (he : candidate.view.eventAt id = some (.ampere (.ordinary kind))) :
    CompleteAt candidate (.base (.tma (.source id))) := by
  intro other hcontrol heffect
  cases other with
  | wgmmaRead issue operand => cases hcontrol
  | base other =>
    cases other with
    | tma source =>
      have heq : source = .source id := Unified.ControlNode.base.inj hcontrol
      subst source
      rfl
    | copyRead actual =>
      have hid : actual = id := Tma.Node.source.inj (Unified.ControlNode.base.inj hcontrol)
      subst actual
      simp [readByte,writeByte,Unified.readByte,Unified.writeByte,Unified.kind,Access.kind,Access.copyAt,he] at heffect
    | copyWrite actual =>
      have hid : actual = id := Tma.Node.source.inj (Unified.ControlNode.base.inj hcontrol)
      subst actual
      simp [readByte,writeByte,Unified.readByte,Unified.writeByte,Unified.kind,Access.kind,Access.copyAt,he] at heffect

theorem ordinary_linked {candidate id kind}
    (he : candidate.view.eventAt id = some (.ampere (.ordinary kind))) :
    Linked candidate (.base (.tma (.source id))) := by
  refine ⟨⟨?_,?_⟩,ordinary_complete_at he⟩
  · intro loc value hr
    exact ⟨.kernel,.kernel (ordinary_read_use hr)⟩
  · intro loc value hw
    exact ⟨.kernel,.kernel (ordinary_write_use hw)⟩

end
end Ptx.Hopper.ByteContents
