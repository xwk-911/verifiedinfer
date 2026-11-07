import Ptx.Event.Consistency

/-! Generic-proxy memory over an explicit access graph. Logical agents and the
physical threads used for scopes are distinct. Source encodings are isomorphic
to optional writer nodes; instances provide proofs, not extra model axioms.
Construct-specific source/barrier/async legality is checked by each adapter. -/
namespace Ptx.MemoryGraph
open Ptx.ISA
open Ptx.Event (Kind Path ByteMap)

class Sources (Node : outParam Type) (Source : Type) where
  decode : Source → Option Node
  encode : Option Node → Source
  decode_encode : ∀ x, decode (encode x) = x
  encode_decode : ∀ x, encode (decode x) = x

instance {Node : Type} : Sources Node (Option Node) where
  decode := id
  encode := id
  decode_encode _ := rfl
  encode_decode _ := rfl

variable {Node ByteValue Source : Type} [Sources Node Source]
def initialSource : Source := Sources.encode (none : Option Node)
def writeSource (node : Node) : Source := Sources.encode (some node)
@[simp] theorem decode_initial : Sources.decode (initialSource (Node := Node) (Source := Source)) = none := Sources.decode_encode _
@[simp] theorem decode_write (node : Node) : Sources.decode (writeSource (Source := Source) node) = some node := Sources.decode_encode _
theorem initial_ne_write (node : Node) : initialSource (Source := Source) ≠ writeSource node := by
  intro he
  have hh := congrArg Sources.decode he
  simp only [decode_initial,decode_write] at hh
  cases hh
theorem write_injective : Function.Injective (writeSource (Node := Node) (Source := Source)) := by
  intro a b he
  have hh := congrArg Sources.decode he
  simpa only [decode_write,Option.some.injEq] using hh
theorem source_cases (source : Source) : source = initialSource (Node := Node) ∨ ∃ node, source = writeSource node := by
  cases hs : (Sources.decode source : Option Node) with
  | none => exact .inl (by simpa only [hs,initialSource,writeSource] using (Sources.encode_decode source).symm)
  | some node => exact .inr ⟨node,by simpa only [hs,initialSource,writeSource] using (Sources.encode_decode source).symm⟩

inductive Agent
  | thread (owner : ThreadId)
  | operation (owner : ThreadId) (family ordinal : Nat)
  deriving Repr, DecidableEq

def Agent.owner : Agent → ThreadId
  | .thread owner | .operation owner _ _ => owner

structure Graph (Node ByteValue : Type) where
  kind : Node → Option (Kind ByteValue)
  present : Node → Prop
  agent : Node → Agent
  po : Node → Node → Prop
  base : Node → Node → Prop
  complete : Prop

def Graph.readByte (c : Graph Node ByteValue) (id : Node) (loc : Location) : Option ByteValue :=
  (c.kind id).bind (fun kind => kind.readByte loc)

def Graph.writeByte (c : Graph Node ByteValue) (id : Node) (loc : Location) : Option ByteValue :=
  (c.kind id).bind (fun kind => kind.writeByte loc)

def Graph.Accesses (c : Graph Node ByteValue) (id : Node) (loc : Location) : Prop :=
  (c.readByte id loc).isSome = true ∨ (c.writeByte id loc).isSome = true

def Graph.Writes (c : Graph Node ByteValue) (id : Node) : Prop :=
  ∃ loc value, c.writeByte id loc = some value

def Graph.Overlap (c : Graph Node ByteValue) (a b : Node) : Prop :=
  ∃ loc, c.Accesses a loc ∧ c.Accesses b loc

def Graph.SameFootprint (c : Graph Node ByteValue) (a b : Node) : Prop :=
  ∃ footprint, (c.kind a).bind Kind.footprint = some footprint ∧
    (c.kind b).bind Kind.footprint = some footprint

theorem access_footprint_bounds {c : Graph Node ByteValue} {id loc base size}
    (ha : c.Accesses id loc) (hf : (c.kind id).bind Kind.footprint = some (base,size)) :
    base.space = loc.space ∧ base.address ≤ loc.address ∧ loc.address < base.address+size := by
  cases he : c.kind id with
  | none => simp [Graph.Accesses,Graph.readByte,Graph.writeByte,he] at ha
  | some kind =>
    cases kind with
    | read start bytes =>
      simp only [he,Option.bind_some,Kind.footprint,Option.some.injEq,Prod.mk.injEq] at hf
      rcases hf with ⟨rfl,rfl⟩
      rcases ha with hr | hw
      · obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp hr
        exact Ptx.Event.payloadByte_bounds (by simpa [Graph.readByte,he,Kind.readByte] using hv)
      · simp [Graph.writeByte,he,Kind.writeByte] at hw
    | write start bytes =>
      simp only [he,Option.bind_some,Kind.footprint,Option.some.injEq,Prod.mk.injEq] at hf
      rcases hf with ⟨rfl,rfl⟩
      rcases ha with hr | hw
      · simp [Graph.readByte,he,Kind.readByte] at hr
      · obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp hw
        exact Ptx.Event.payloadByte_bounds (by simpa [Graph.writeByte,he,Kind.writeByte] using hv)
    | rmw scope start bytes =>
      simp only [he,Option.bind_some,Kind.footprint,Option.some.injEq,Prod.mk.injEq] at hf
      rcases hf with ⟨rfl,rfl⟩
      rcases ha with hr | hw
      · obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp hr
        exact Ptx.Event.payloadByte_bounds (by simpa [Graph.readByte,he,Kind.readByte] using hv)
      · obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp hw
        have hb := Ptx.Event.payloadByte_bounds (by simpa [Graph.writeByte,he,Kind.writeByte] using hv)
        simpa only [bytes.sameSize] using hb
    | barrierArrival bid generation => simp [he,Kind.footprint] at hf
    | barrierReturn bid generation => simp [he,Kind.footprint] at hf

def Graph.IsRMW (c : Graph Node ByteValue) (id : Node) : Prop :=
  ∃ scope base bytes, c.kind id = some (.rmw scope base bytes)

/-- Ordinary reads/writes are exclusive; a true RMW has both projections. -/
theorem read_write_requires_rmw {c : Graph Node ByteValue} {id readLoc writeLoc readValue writeValue}
    (hr : Graph.readByte c id readLoc = some readValue)
    (hw : Graph.writeByte c id writeLoc = some writeValue) : c.IsRMW id := by
  cases he : c.kind id with
  | none => simp [Graph.readByte,he] at hr
  | some kind =>
    cases kind with
    | rmw scope base bytes => exact ⟨scope,base,bytes,he⟩
    | _ => simp [Graph.readByte,Graph.writeByte,he,Kind.readByte,Kind.writeByte] at hr hw

theorem read_write_exclusive {c : Graph Node ByteValue} {id readLoc writeLoc readValue writeValue}
    (hn : ¬ c.IsRMW id) (hr : c.readByte id readLoc = some readValue)
    (hw : c.writeByte id writeLoc = some writeValue) : False :=
  hn (read_write_requires_rmw hr hw)

def sourceByte (c : Graph Node ByteValue) (initial : ByteMap ByteValue) (loc : Location) (source : Source) : Option ByteValue :=
  match Sources.decode source with | none => some (initial loc) | some node => c.writeByte node loc
@[simp] theorem sourceByte_initial (c : Graph Node ByteValue) (initial : ByteMap ByteValue) (loc : Location) :
    sourceByte c initial loc (initialSource (Node := Node) (Source := Source)) = some (initial loc) := by simp [sourceByte]
@[simp] theorem sourceByte_write (c : Graph Node ByteValue) (initial : ByteMap ByteValue) (loc : Location) (node : Node) :
    sourceByte c initial loc (writeSource (Source := Source) node) = c.writeByte node loc := by simp [sourceByte]

abbrev ReadsFrom (Node Source : Type) := Node → Location → Source
abbrev Coherence (Source : Type) := Location → Source → Source → Prop

def ValueAgreement (c : Graph Node ByteValue) (initial : ByteMap ByteValue)
    (eligible : Node → Location → Prop) (rf : ReadsFrom Node Source) : Prop :=
  ∀ read loc value, eligible read loc → c.readByte read loc = some value →
    sourceByte c initial loc (rf read loc) = some value

def BaseAcyclic (c : Graph Node ByteValue) : Prop := ∀ node, ¬ c.base node node

def MutuallyScoped (c : Graph Node ByteValue) (a b : Node) : Prop :=
  ∃ sa sb, (c.kind a).bind Kind.strongScope = some sa ∧
    (c.kind b).bind Kind.strongScope = some sb ∧
    sa.Includes (c.agent a).owner (c.agent b).owner ∧ sb.Includes (c.agent b).owner (c.agent a).owner

/-- The current instructions all use the generic proxy. Both operations must
include one another's thread, and their byte footprints must match completely. -/
def MorallyStrong (c : Graph Node ByteValue) (a b : Node) : Prop :=
  (c.agent a = c.agent b ∨ MutuallyScoped c a b) ∧ c.SameFootprint a b

theorem scope_requires_rmw {c : Graph Node ByteValue} {event scope}
    (hs : (c.kind event).bind Kind.strongScope = some scope) : c.IsRMW event := by
  cases he : c.kind event with
  | none => simp [he] at hs
  | some kind =>
    cases kind with
    | rmw s base bytes => exact ⟨s,base,bytes,he⟩
    | _ => simp [he,Kind.strongScope] at hs

theorem morally_strong_of_no_rmw {c : Graph Node ByteValue} {a b}
    (hn : ¬ c.IsRMW a) : MorallyStrong c a b ↔ c.agent a = c.agent b ∧ c.SameFootprint a b := by
  constructor
  · rintro ⟨he | ⟨_,_,hs,_,_,_⟩,hf⟩
    · exact ⟨he,hf⟩
    · exact (hn (scope_requires_rmw hs)).elim
  · rintro ⟨he,hf⟩; exact ⟨Or.inl he,hf⟩

theorem write_self_strong {c : Graph Node ByteValue} {event loc value}
    (hw : c.writeByte event loc = some value) : MorallyStrong c event event := by
  cases he : c.kind event with
  | none => simp [Graph.writeByte,he] at hw
  | some kind =>
    cases kind with
    | write base bytes =>
      exact ⟨Or.inl rfl,(base,bytes.length),by simp [he,Kind.footprint],by simp [he,Kind.footprint]⟩
    | rmw scope base bytes =>
      exact ⟨Or.inl rfl,(base,bytes.before.length),by simp [he,Kind.footprint],by simp [he,Kind.footprint]⟩
    | read base bytes => simp [Graph.writeByte,he,Kind.writeByte] at hw
    | barrierArrival bid generation => simp [Graph.writeByte,he,Kind.writeByte] at hw
    | barrierReturn bid generation => simp [Graph.writeByte,he,Kind.writeByte] at hw

def Observed (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) (write read : Node) : Prop :=
  MorallyStrong c write read ∧ ∃ loc value,
    c.readByte read loc = some value ∧ rf read loc = writeSource write ∧
    (c.writeByte write loc).isSome = true

/-- Observation may pass through RMWs, but not through arbitrary intervening
reads/writes. Relaxed observation is not itself cross-thread causality. -/
inductive ObservationOrder (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) : Node → Node → Prop
  | direct {a b} : Observed c rf a b → ObservationOrder c rf a b
  | viaRMW {a middle b} : c.IsRMW middle → ObservationOrder c rf a middle →
      ObservationOrder c rf middle b → ObservationOrder c rf a b

theorem observation_order_of_no_rmw {c : Graph Node ByteValue} {rf : ReadsFrom Node Source} {a b}
    (hn : ∀ event, ¬ c.IsRMW event) : ObservationOrder c rf a b ↔ Observed c rf a b := by
  constructor
  · intro ho
    cases ho with
    | direct h => exact h
    | viaRMW hm _ _ => exact (hn _ hm).elim
  · exact ObservationOrder.direct

def ProxyPreservedBase (c : Graph Node ByteValue) (a b : Node) : Prop :=
  c.Overlap a b ∧ c.base a b

/-- Causality is not closed transitively beyond the ISA's definition. -/
def Causality (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) (a b : Node) : Prop :=
  ProxyPreservedBase c a b ∨
    ∃ middle, ObservationOrder c rf a middle ∧ ProxyPreservedBase c middle b

structure DataRace (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) (a b : Node) : Prop where
  overlap : c.Overlap a b
  conflict : c.Writes a ∨ c.Writes b
  notForward : ¬ Causality c rf a b
  notBackward : ¬ Causality c rf b a
  notStrong : ¬ MorallyStrong c a b

def MixedSizeRace (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) : Prop :=
  ∃ a b, DataRace c rf a b ∧ ¬ c.SameFootprint a b

/-- A read is also tainted by racing writes to a byte it reads, even when that
read does not itself race with either write. Mixed-size races disable all the
memory-model conditions below, rather than being silently filtered out. -/
def Tainted (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) (read : Node) (loc : Location) : Prop :=
  (∃ write, (c.writeByte write loc).isSome = true ∧ DataRace c rf read write) ∨
  (∃ a b, (c.writeByte a loc).isSome = true ∧ (c.writeByte b loc).isSome = true ∧
    DataRace c rf a b)

def Eligible (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) (read : Node) (loc : Location) : Prop :=
  ¬ MixedSizeRace c rf ∧ ¬ Tainted c rf read loc


structure Coherent (c : Graph Node ByteValue) (initial : ByteMap ByteValue) (rf : ReadsFrom Node Source)
    (co : Coherence Source) : Prop where
  irrefl : ∀ loc a, ¬ co loc a a
  transitive : ∀ loc a b d, co loc a b → co loc b d → co loc a d
  domain : ∀ loc a b, co loc a b →
    (sourceByte c initial loc a).isSome = true ∧ (sourceByte c initial loc b).isSome = true
  initialization : ∀ loc writer value, c.writeByte writer loc = some value →
    co loc initialSource (writeSource writer)
  comparable : ∀ loc a b va vb, a ≠ b →
    c.writeByte a loc = some va → c.writeByte b loc = some vb →
    (MorallyStrong c a b ∨ Causality c rf a b ∨ Causality c rf b a) →
    co loc (writeSource a) (writeSource b) ∨ co loc (writeSource b) (writeSource a)
  raceUnordered : ∀ loc a b, DataRace c rf a b →
    ¬ co loc (writeSource a) (writeSource b)
  causality : ∀ loc a b va vb, c.writeByte a loc = some va →
    c.writeByte b loc = some vb → Causality c rf a b → co loc (writeSource a) (writeSource b)

structure CausalityConditions (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) (co : Coherence Source) : Prop where
  noFuture : ∀ read writer loc vr vw, c.readByte read loc = some vr →
    c.writeByte writer loc = some vw → Causality c rf read writer →
    rf read loc ≠ writeSource writer
  noStale : ∀ writer read loc vw vr, c.writeByte writer loc = some vw →
    c.readByte read loc = some vr → Causality c rf writer read →
    ¬ co loc (rf read loc) (writeSource writer)

def SingleCopyAtomicity (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) (co : Coherence Source) : Prop :=
  ∀ read writer, MorallyStrong c read writer →
    ∀ loc vr vw, c.readByte read loc = some vr → c.writeByte writer loc = some vw →
      rf read loc = writeSource writer →
      ∀ other vr' vw', c.readByte read other = some vr' →
        c.writeByte writer other = some vw' → ¬ co other (rf read other) (writeSource writer)

/-- An RMW cannot read before a morally strong overlapping modification that
precedes its own write. The source byte and ordering byte may differ. -/
def RMWAtomicity (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) (co : Coherence Source) : Prop :=
  ∀ atomic writer, c.IsRMW atomic → MorallyStrong c atomic writer →
    ∀ loc vr vw, c.readByte atomic loc = some vr → c.writeByte writer loc = some vw →
      co loc (rf atomic loc) (writeSource writer) →
      ∀ other va vb, c.writeByte atomic other = some va → c.writeByte writer other = some vb →
        ¬ co other (writeSource writer) (writeSource atomic)

def Communication (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) (co : Coherence Source)
    (a b : Node) : Prop :=
  (∃ loc value, c.readByte b loc = some value ∧ rf b loc = writeSource a ∧
    (c.writeByte a loc).isSome = true) ∨
  (∃ loc, co loc (writeSource a) (writeSource b)) ∨
  -- An unsplit RMW's internal read-to-own-write step is not an inter-operation
  -- from-read edge. Reads-from-self remains represented by the first case.
  (a ≠ b ∧ ∃ loc value, c.readByte a loc = some value ∧ co loc (rf a loc) (writeSource b))

/-- SC-per-location applies within pairwise morally strong overlapping slices,
not to all communication between arbitrary weak accesses in the grid. -/
def SCPerLocation (c : Graph Node ByteValue) (rf : ReadsFrom Node Source) (co : Coherence Source) : Prop :=
  ∀ members : Node → Prop,
    (∀ a, members a → c.present a) →
    (∀ a b, members a → members b → MorallyStrong c a b ∧ c.Overlap a b) →
    ∀ a, members a → ¬ Path (fun x y => members x ∧ members y ∧
      (c.po x y ∨ Communication c rf co x y)) a a

/-- Current generic memory constraints. Mixed-size races relax the memory
conditions; they do not make the candidate disappear. Complete kernel correctness
additionally needs provenance, API observation and explicit launch preconditions. -/
structure MemoryConditions (c : Graph Node ByteValue) (initial : ByteMap ByteValue)
    (rf : ReadsFrom Node Source) (co : Coherence Source) : Prop where
  baseAcyclic : BaseAcyclic c
  agreement : ValueAgreement c initial (Eligible c rf) rf
  coherence : ¬ MixedSizeRace c rf → Coherent c initial rf co
  causality : ¬ MixedSizeRace c rf → CausalityConditions c rf co
  atomicity : ¬ MixedSizeRace c rf → SingleCopyAtomicity c rf co
  scPerLocation : ¬ MixedSizeRace c rf → SCPerLocation c rf co
  rmwAtomicity : ¬ MixedSizeRace c rf → RMWAtomicity c rf co


end Ptx.MemoryGraph
