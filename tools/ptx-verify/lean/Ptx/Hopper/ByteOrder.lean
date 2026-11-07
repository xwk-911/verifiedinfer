import Ptx.Hopper.ProxyPublication
import Ptx.MemoryGraph.Core

/-! Byte-indexed Hopper ordering and proxy-aware race/eligibility components.
The inventory facade reuses only access/footprint facts from MemoryGraph. Its
generic-only strength/causality predicates are not the ones defined here.
Keeping the byte fixed across a path prevents a shared proxy fence from
publishing an unrelated global-memory location through a TMA completion.
This is not complete PTX/ISA/observer admission or a hardware conformance proof. -/
namespace Ptx.Hopper.Access
open Ptx.ISA
noncomputable section

def Node.owner : Node → ThreadId
  | .tma (.source event) => event.thread
  | .tma (.descriptor id) | .tma (.read id _) | .tma (.write id _) | .tma (.notify id) => id.issue.thread
  | .copyRead event | .copyWrite event => event.thread

def Node.memoryAgent : Node → MemoryGraph.Agent
  | .tma (.source event) => .thread event.thread
  | .tma (.descriptor id) => .operation id.issue.thread 1 id.issue.serial
  | .tma (.read id _) | .tma (.write id _) => .operation id.issue.thread 2 id.issue.serial
  | .tma (.notify id) => .operation id.issue.thread 3 id.issue.serial
  | .copyRead event | .copyWrite event => .operation event.thread 0 event.serial

def inventoryGraph (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) : MemoryGraph.Graph Node Symbolic.Byte := {
  kind := kind resolve descriptor c
  present := Present c
  agent := Node.memoryAgent
  po := ProgramOrder c
  base := fun _ _ => False
  complete := Complete c
}

def Accesses (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) (node : Node) (loc : Location) : Prop :=
  (readByte resolve descriptor c node loc).isSome = true ∨ (writeByte resolve descriptor c node loc).isSome = true
def WritesAt (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) (node : Node) (loc : Location) : Prop :=
  (writeByte resolve descriptor c node loc).isSome = true
def SameFootprint (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) (a b : Node) : Prop := (inventoryGraph resolve descriptor c).SameFootprint a b

def MutuallyScoped (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) (a b : Node) : Prop :=
  ∃ sa sb, (kind resolve descriptor c a).bind Ptx.Event.Kind.strongScope = some sa ∧
    (kind resolve descriptor c b).bind Ptx.Event.Kind.strongScope = some sb ∧
    sa.Includes a.owner b.owner ∧ sb.Includes b.owner a.owner
def MorallyStrong (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) (a b : Node) : Prop :=
  a.proxy = b.proxy ∧ (a.agent = b.agent ∨ MutuallyScoped resolve descriptor c a b) ∧ SameFootprint resolve descriptor c a b

/-- No implicit accesses are placed in the issuer's program order. -/
def NonbulkInternal (c : Candidate) : Node → Node → Prop
  | .copyRead a,.copyWrite b => a = b ∧ (copyAt c a).isSome = true
  | _,_ => False
def NonbulkCompleted (c : Candidate) : Node → Node → Prop
  | .copyWrite issue,.tma (.source wait) => issue.thread = wait.thread ∧ ∃ op groups keep,
      copyAt c issue = some op ∧ c.eventAt wait = some (.ampere (.wait groups keep)) ∧ op.group < groups-keep
  | _,_ => False
def TensorInternal (c : Candidate) : Node → Node → Prop
  | .tma (.read a offset),.tma (.write b other) => a = b ∧ offset = other ∧ (Tma.readLocation c a offset).isSome = true
  | _,_ => False

def ByteEdge (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (loc : Location) (a b : Node) : Prop :=
  (match a,b with | .tma (.source x),.tma (.source y) => GenericEdge c x y | _,_ => False) ∨
  NonbulkInternal c a b ∨ NonbulkCompleted c a b ∨ TensorInternal c a b ∨
  Published resolve c histories cluster a b loc ∨ Protected resolve c a b loc

def ByteOrder (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (loc : Location) :=
  Ptx.Event.Path (ByteEdge resolve descriptor c histories cluster loc)

def Observed (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) (rf : ReadsFrom) (writer read : Node) : Prop :=
  MorallyStrong resolve descriptor c writer read ∧ ∃ loc value,
    readByte resolve descriptor c read loc = some value ∧ rf read loc = some writer ∧ WritesAt resolve descriptor c writer loc
inductive ObservationOrder (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate) (rf : ReadsFrom) : Node → Node → Prop
  | direct {a b} : Observed resolve descriptor c rf a b → ObservationOrder resolve descriptor c rf a b
  | viaRMW {a middle b} : (inventoryGraph resolve descriptor c).IsRMW middle →
      ObservationOrder resolve descriptor c rf a middle → ObservationOrder resolve descriptor c rf middle b →
      ObservationOrder resolve descriptor c rf a b

/-- Observation may prefix byte-preserved order. This is not its arbitrary
transitive closure through reads/writes or through other byte locations. -/
def CausalityAt (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (rf : ReadsFrom) (loc : Location) (a b : Node) : Prop :=
  (Accesses resolve descriptor c a loc ∧ Accesses resolve descriptor c b loc ∧ ByteOrder resolve descriptor c histories cluster loc a b) ∨
  ∃ middle, ObservationOrder resolve descriptor c rf a middle ∧
    Accesses resolve descriptor c middle loc ∧ Accesses resolve descriptor c b loc ∧ ByteOrder resolve descriptor c histories cluster loc middle b

structure DataRaceAt (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (rf : ReadsFrom) (loc : Location) (a b : Node) : Prop where
  left : Accesses resolve descriptor c a loc
  right : Accesses resolve descriptor c b loc
  conflict : WritesAt resolve descriptor c a loc ∨ WritesAt resolve descriptor c b loc
  notForward : ¬ CausalityAt resolve descriptor c histories cluster rf loc a b
  notBackward : ¬ CausalityAt resolve descriptor c histories cluster rf loc b a
  notStrong : ¬ MorallyStrong resolve descriptor c a b

def MixedSizeRace (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (rf : ReadsFrom) : Prop :=
  ∃ loc a b, DataRaceAt resolve descriptor c histories cluster rf loc a b ∧ ¬ SameFootprint resolve descriptor c a b
def Tainted (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (rf : ReadsFrom) (read : Node) (loc : Location) : Prop :=
  (∃ writer, WritesAt resolve descriptor c writer loc ∧ DataRaceAt resolve descriptor c histories cluster rf loc read writer) ∨
  (∃ a b, WritesAt resolve descriptor c a loc ∧ WritesAt resolve descriptor c b loc ∧
    DataRaceAt resolve descriptor c histories cluster rf loc a b)
def Eligible (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (rf : ReadsFrom) (read : Node) (loc : Location) : Prop :=
  ¬ MixedSizeRace resolve descriptor c histories cluster rf ∧ ¬ Tainted resolve descriptor c histories cluster rf read loc

theorem strong_same_proxy {resolve descriptor c a b} (h : MorallyStrong resolve descriptor c a b) : a.proxy = b.proxy := h.1

theorem write_self_strong {resolve descriptor c node loc value}
    (hw : writeByte resolve descriptor c node loc = some value) : MorallyStrong resolve descriptor c node node := by
  have hh := MemoryGraph.write_self_strong (c := inventoryGraph resolve descriptor c) hw
  exact ⟨rfl,.inl rfl,hh.2⟩

theorem strong_symm {resolve descriptor c a b} (h : MorallyStrong resolve descriptor c a b) : MorallyStrong resolve descriptor c b a := by
  refine ⟨h.1.symm,?_,?_⟩
  · rcases h.2.1 with he | ⟨sa,sb,ha,hb,hsa,hsb⟩
    · exact .inl he.symm
    · exact .inr ⟨sb,sa,hb,ha,hsb,hsa⟩
  · obtain ⟨footprint,ha,hb⟩ := h.2.2
    exact ⟨footprint,hb,ha⟩

theorem published_byte_order {resolve descriptor c histories cluster a b loc}
    (h : Published resolve c histories cluster a b loc) : ByteOrder resolve descriptor c histories cluster loc a b :=
  .single (.inr (.inr (.inr (.inr (.inl h)))))
theorem protected_byte_order {resolve descriptor c histories cluster a b loc}
    (h : Protected resolve c a b loc) : ByteOrder resolve descriptor c histories cluster loc a b :=
  .single (.inr (.inr (.inr (.inr (.inr h)))))
theorem byte_order_causal {resolve descriptor c histories cluster rf a b loc}
    (ha : Accesses resolve descriptor c a loc) (hb : Accesses resolve descriptor c b loc)
    (ho : ByteOrder resolve descriptor c histories cluster loc a b) : CausalityAt resolve descriptor c histories cluster rf loc a b :=
  .inl ⟨ha,hb,ho⟩

theorem ordered_conflicts_no_races {resolve descriptor c histories cluster rf}
    (ho : ∀ writer other loc, WritesAt resolve descriptor c writer loc → Accesses resolve descriptor c other loc →
      writer = other ∨ ByteOrder resolve descriptor c histories cluster loc writer other ∨ ByteOrder resolve descriptor c histories cluster loc other writer) :
    ∀ loc a b, ¬ DataRaceAt resolve descriptor c histories cluster rf loc a b := by
  intro loc a b hr
  rcases hr.conflict with hw | hw
  · rcases ho a b loc hw hr.right with he | hf | hb
    · subst b
      obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hw
      exact hr.notStrong (write_self_strong hvalue)
    · exact hr.notForward (byte_order_causal hr.left hr.right hf)
    · exact hr.notBackward (byte_order_causal hr.right hr.left hb)
  · rcases ho b a loc hw hr.left with he | hf | hb
    · subst a
      obtain ⟨value,hvalue⟩ := Option.isSome_iff_exists.mp hw
      exact hr.notStrong (write_self_strong hvalue)
    · exact hr.notBackward (byte_order_causal hr.right hr.left hf)
    · exact hr.notForward (byte_order_causal hr.left hr.right hb)

theorem race_free_eligible {resolve descriptor c histories cluster rf}
    (hn : ∀ loc a b, ¬ DataRaceAt resolve descriptor c histories cluster rf loc a b) (read loc) :
    Eligible resolve descriptor c histories cluster rf read loc := by
  constructor
  · rintro ⟨loc,a,b,hr,_⟩; exact hn loc a b hr
  · rintro (⟨_,_,hr⟩ | ⟨_,_,_,_,hr⟩) <;> exact hn _ _ _ hr

theorem global_edge_from_source {resolve descriptor c histories cluster address event target}
    (h : ByteEdge resolve descriptor c histories cluster ⟨.global,address⟩ (.tma (.source event)) target) :
    ∃ other, target = .tma (.source other) := by
  cases target with
  | copyRead _ | copyWrite _ => simp [ByteEdge,NonbulkInternal,NonbulkCompleted,TensorInternal,Published,Protected] at h
  | tma node =>
    cases node with
    | source other => exact ⟨other,rfl⟩
    | descriptor _ | read _ _ | write _ _ | notify _ =>
      simp [ByteEdge,NonbulkInternal,NonbulkCompleted,TensorInternal,Published,Protected] at h

theorem global_order_from_source {resolve descriptor c histories cluster address a b}
    (h : ByteOrder resolve descriptor c histories cluster ⟨.global,address⟩ a b)
    (hs : ∃ event, a = .tma (.source event)) : ∃ event, b = .tma (.source event) := by
  induction h with
  | single he => obtain ⟨event,rfl⟩ := hs; exact global_edge_from_source he
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hs)

theorem no_global_source_to_tensor_write {resolve descriptor c histories cluster address event id offset} :
    ¬ ByteOrder resolve descriptor c histories cluster ⟨.global,address⟩ (.tma (.source event)) (.tma (.write id offset)) := by
  intro ho
  obtain ⟨other,hh⟩ := global_order_from_source ho ⟨event,rfl⟩
  cases hh

theorem no_fence_edge_from_source {resolve descriptor c histories cluster loc event target}
    (hn : ∀ fence cta, c.eventAt fence ≠ some (.proxyFenceAsyncShared cta))
    (h : ByteEdge resolve descriptor c histories cluster loc (.tma (.source event)) target) :
    ∃ other, target = .tma (.source other) := by
  cases target with
  | copyRead _ | copyWrite _ => simp [ByteEdge,NonbulkInternal,NonbulkCompleted,TensorInternal,Published,Protected] at h
  | tma node =>
    cases node with
    | source other => exact ⟨other,rfl⟩
    | descriptor _ | read _ _ | notify _ => simp [ByteEdge,NonbulkInternal,NonbulkCompleted,TensorInternal,Published,Protected] at h
    | write id offset => simp [ByteEdge,NonbulkInternal,NonbulkCompleted,TensorInternal,Published,Protected,hn] at h

theorem no_fence_order_from_source {resolve descriptor c histories cluster loc a b}
    (hn : ∀ fence cta, c.eventAt fence ≠ some (.proxyFenceAsyncShared cta))
    (h : ByteOrder resolve descriptor c histories cluster loc a b)
    (hs : ∃ event, a = .tma (.source event)) : ∃ event, b = .tma (.source event) := by
  induction h with
  | single he => obtain ⟨event,rfl⟩ := hs; exact no_fence_edge_from_source hn he
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hs)

theorem tensor_write_first_publication {resolve descriptor c histories cluster loc a b}
    (h : ByteOrder resolve descriptor c histories cluster loc a b) :
    ∀ id offset, a = .tma (.write id offset) → ∃ target, Published resolve c histories cluster a target loc := by
  induction h with
  | @single a b he =>
    intro id offset ha
    subst a
    refine ⟨b,?_⟩
    rcases he with hg | hi | hc | ht | hp | hf
    · cases b <;> simp_all
    · cases b <;> simp_all [NonbulkInternal]
    · cases b <;> simp_all [NonbulkCompleted]
    · cases b <;> simp_all [TensorInternal]
    · exact hp
    · cases b <;> simp_all [Protected]
  | trans _ _ ih _ => exact ih

theorem initial_rf_no_observation {resolve descriptor c a b} :
    ¬ ObservationOrder resolve descriptor c (fun _ _ => none) a b := by
  intro ho
  induction ho with
  | direct he => obtain ⟨_,_,_,_,hs,_⟩ := he; cases hs
  | viaRMW _ _ _ ih _ => exact ih

theorem mixed_size_disables_eligibility {resolve descriptor c histories cluster rf}
    (hm : MixedSizeRace resolve descriptor c histories cluster rf) (read loc) :
    ¬ Eligible resolve descriptor c histories cluster rf read loc := fun he => he.1 hm

/-- A source region remains closed when generic edges preserve it and no
shared proxy fence can lead from it to a later transfer. This is a proof rule
over actual edges, not an extra execution restriction. -/
theorem source_region_edge {resolve descriptor c histories cluster loc event target}
    (region : Ptx.Event.EventId → Prop)
    (hg : ∀ a b, region a → GenericEdge c a b → region b)
    (hf : ∀ a b, region a → ¬ Protected resolve c (.tma (.source a)) b loc)
    (hs : region event)
    (he : ByteEdge resolve descriptor c histories cluster loc (.tma (.source event)) target) :
    ∃ other, target = .tma (.source other) ∧ region other := by
  cases target with
  | copyRead _ | copyWrite _ => simp [ByteEdge,NonbulkInternal,NonbulkCompleted,TensorInternal,Published,Protected] at he
  | tma node =>
    cases node with
    | source other =>
      have hh : GenericEdge c event other := by
        simpa [ByteEdge,NonbulkInternal,NonbulkCompleted,TensorInternal,Published,Protected] using he
      exact ⟨other,rfl,hg event other hs hh⟩
    | descriptor _ | read _ _ | notify _ => simp [ByteEdge,NonbulkInternal,NonbulkCompleted,TensorInternal,Published,Protected] at he
    | write id offset =>
      have hp : Protected resolve c (.tma (.source event)) (.tma (.write id offset)) loc := by
        simpa [ByteEdge,NonbulkInternal,NonbulkCompleted,TensorInternal,Published,Protected] using he
      exact (hf event _ hs hp).elim

theorem source_region_order {resolve descriptor c histories cluster loc a b}
    (region : Ptx.Event.EventId → Prop)
    (hg : ∀ x y, region x → GenericEdge c x y → region y)
    (hf : ∀ x y, region x → ¬ Protected resolve c (.tma (.source x)) y loc)
    (ho : ByteOrder resolve descriptor c histories cluster loc a b)
    (hs : ∃ event, a = .tma (.source event) ∧ region event) :
    ∃ event, b = .tma (.source event) ∧ region event := by
  induction ho with
  | single he => obtain ⟨event,rfl,hs⟩ := hs; exact source_region_edge region hg hf hs he
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hs)

theorem observation_order_absent {resolve descriptor c rf}
    (hn : ∀ a b, ¬ Observed resolve descriptor c rf a b) : ∀ a b, ¬ ObservationOrder resolve descriptor c rf a b := by
  intro a b ho
  induction ho with
  | direct he => exact hn _ _ he
  | viaRMW _ _ _ ih _ => exact ih

end
end Ptx.Hopper.Access
