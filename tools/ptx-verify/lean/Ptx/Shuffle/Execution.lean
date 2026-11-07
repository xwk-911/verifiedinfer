import Ptx.Shuffle.Thread
import Ptx.Scalar.Execution

/-! Launch-wide shuffle provenance, rendezvous and value agreement. Dynamic
generations are computed per (mode,membermask) by actual source execution.
Different static PCs may rendezvous on sm_70+. Named peers that have exited
before this generation need not arrive, but an absent/inactive source cannot
supply a defined register result. Undefined groups retain unconstrained oracle
value/predicate results. Definedness is a separate safety obligation.
Shuffle rendezvous introduces no memory-barrier edge into the ordinary graph.
-/
namespace Ptx.Shuffle
open Ptx.ISA
noncomputable section

structure ThreadTrace where
  id : ThreadId
  oracle : Oracle
  count : Nat
  final : State
  events : List Kind
structure Candidate where
  traces : List ThreadTrace

def Produced (code : List Instr) (params : Bindings) (block : Dim3) (trace : ThreadTrace) : Prop :=
  run {id := trace.id,params := params,block := block} trace.oracle code trace.count {} = .ok (trace.final,trace.events)
def WellFormed (code : List Instr) (launch : Scalar.Launch) (candidate : Candidate) : Prop :=
  launch.geometry.Valid ∧ (candidate.traces.map ThreadTrace.id).Nodup ∧
  (∀ trace ∈ candidate.traces, trace.id.Valid launch.geometry ∧ Produced code launch.params launch.geometry.block trace) ∧
  ∀ id, id.Valid launch.geometry → ∃ trace ∈ candidate.traces, trace.id = id
def Complete (candidate : Candidate) : Prop := ∀ trace ∈ candidate.traces, trace.final.base.core.thread.status = .done

def Candidate.eventAt (candidate : Candidate) (id : Event.EventId) : Option Kind :=
  (candidate.traces.find? (fun trace => trace.id == id.thread)).bind (fun trace => trace.events[id.serial]?)
def Candidate.shuffleAt (candidate : Candidate) (id : Event.EventId) : Option Record :=
  (candidate.eventAt id).bind (fun event => match event with | .shuffle record => some record | .ordinary _ => none)
def ordinaryEvents (events : List Kind) : List Scalar.Kind := events.filterMap (fun event => match event with
  | .ordinary event => some event
  | .shuffle _ => none)
def Candidate.view (candidate : Candidate) : Event.Candidate Symbolic.Byte Oracle :=
  ⟨candidate.traces.map (fun trace => ⟨trace.id,trace.oracle,trace.count,trace.final.base.core,ordinaryEvents trace.events⟩)⟩

def Arrived (candidate : Candidate) (thread : ThreadId) (key : Key) (generation : Nat) : Prop :=
  ∃ serial record, candidate.shuffleAt ⟨thread,serial⟩ = some record ∧ record.key = key ∧ record.generation = generation
def ExitedBefore (trace : ThreadTrace) (key : Key) (groupGeneration : Nat) : Prop :=
  trace.final.base.core.thread.status = .done ∧ generation trace.final key ≤ groupGeneration
def Matched (block : Dim3) (candidate : Candidate) (origin : Event.EventId) (record : Record) : Prop :=
  member record.key.mask (lane block origin.thread) = true ∧
  ∀ trace ∈ candidate.traces, SameWarp block origin.thread trace.id → member record.key.mask (lane block trace.id) = true →
    Arrived candidate trace.id record.key record.generation ∨ ExitedBefore trace record.key record.generation
def Source (block : Dim3) (origin : Event.EventId) (record : Record) (peer : Event.EventId) (input : Record) : Prop :=
  SameWarp block origin.thread peer.thread ∧ lane block peer.thread = (select record.key.mode (lane block origin.thread) record.b record.c).source ∧
  member record.key.mask (lane block peer.thread) = true ∧ input.key = record.key ∧ input.generation = record.generation
def Defined (block : Dim3) (candidate : Candidate) : Prop :=
  ∀ origin record, candidate.shuffleAt origin = some record → Matched block candidate origin record ∧
    ∃ peer input, candidate.shuffleAt peer = some input ∧ Source block origin record peer input
def Agreement (block : Dim3) (candidate : Candidate) : Prop :=
  ∀ origin record, candidate.shuffleAt origin = some record → Matched block candidate origin record →
    ∀ peer input, candidate.shuffleAt peer = some input → Source block origin record peer input →
      record.reply = input.input ∧ record.replyPredicate = (select record.key.mode (lane block origin.thread) record.b record.c).predicate

inductive ControlNode
  | arrival (id : Event.EventId)
  | returned (id : Event.EventId)
  | ordinary (id : Event.EventId)
  | exited (thread : ThreadId)
  deriving Repr, DecidableEq
def startNode (id : Event.EventId) : Kind → ControlNode
  | .shuffle _ => .arrival id
  | .ordinary _ => .ordinary id
def finishNode (id : Event.EventId) : Kind → ControlNode
  | .shuffle _ => .returned id
  | .ordinary _ => .ordinary id

/-- This graph constrains execution waits only. It is not added to the
ordinary memory graph's synchronizes-with relation. The exit edge prevents
mutually waiting lanes from both claiming the other has already exited. -/
inductive ControlEdge (block : Dim3) (candidate : Candidate) : ControlNode → ControlNode → Prop
  | local {id record} (he : candidate.shuffleAt id = some record) : ControlEdge block candidate (.arrival id) (.returned id)
  | po {left right before after} (hl : candidate.eventAt left = some before) (hr : candidate.eventAt right = some after)
      (ht : left.thread = right.thread) (hs : left.serial < right.serial) :
      ControlEdge block candidate (finishNode left before) (startNode right after)
  | exit {id event trace} (he : candidate.eventAt id = some event) (ht : trace ∈ candidate.traces)
      (hid : trace.id = id.thread) (hd : trace.final.base.core.thread.status = .done) :
      ControlEdge block candidate (finishNode id event) (.exited trace.id)
  | rendezvous {id record peer input} (he : candidate.shuffleAt id = some record) (hp : candidate.shuffleAt peer = some input)
      (hw : SameWarp block id.thread peer.thread) (hm : member record.key.mask (lane block peer.thread) = true)
      (hk : input.key = record.key) (hg : input.generation = record.generation) :
      ControlEdge block candidate (.arrival peer) (.returned id)
  | exitedPeer {id record trace} (he : candidate.shuffleAt id = some record) (ht : trace ∈ candidate.traces)
      (hw : SameWarp block id.thread trace.id) (hm : member record.key.mask (lane block trace.id) = true)
      (hx : ExitedBefore trace record.key record.generation) : ControlEdge block candidate (.exited trace.id) (.returned id)
  | barrier {left right bid generation} (hl : candidate.eventAt left = some (.ordinary (.barrierArrival bid generation)))
      (hr : candidate.eventAt right = some (.ordinary (.barrierReturn bid generation))) (ht : left.thread.cta = right.thread.cta) :
      ControlEdge block candidate (.ordinary left) (.ordinary right)

def ControlAdmitted (block : Dim3) (candidate : Candidate) : Prop := ∀ node, ¬Event.Path (ControlEdge block candidate) node node

theorem control_admitted_of_rank {block candidate} (rank : ControlNode → Nat)
    (hr : ∀ left right, ControlEdge block candidate left right → rank left < rank right) : ControlAdmitted block candidate := by
  intro node hp
  exact Nat.lt_irrefl _ (hp.rank_lt rank hr)

theorem produced_runs {code params block trace} (hp : Produced code params block trace) :
    Runs {id := trace.id,params := params,block := block} trace.oracle code {} trace.events trace.final := run_sound hp

theorem defined_transfer {block candidate origin record} (ha : Agreement block candidate) (hd : Defined block candidate)
    (hr : candidate.shuffleAt origin = some record) :
    ∃ peer input, candidate.shuffleAt peer = some input ∧ Source block origin record peer input ∧ record.reply = input.input ∧
      record.replyPredicate = (select record.key.mode (lane block origin.thread) record.b record.c).predicate := by
  obtain ⟨hm,peer,input,hinput,hsource⟩ := hd origin record hr
  exact ⟨peer,input,hinput,hsource,ha origin record hr hm peer input hinput hsource⟩

theorem defined_caller_participates {block candidate origin record} (hd : Defined block candidate)
    (hr : candidate.shuffleAt origin = some record) : member record.key.mask (lane block origin.thread) = true := (hd origin record hr).1.1

theorem defined_source_is_in_same_cta_and_warp {block candidate origin record} (hd : Defined block candidate)
    (hr : candidate.shuffleAt origin = some record) :
    ∃ peer input, candidate.shuffleAt peer = some input ∧ origin.thread.cta = peer.thread.cta ∧
      linear block origin.thread / 32 = linear block peer.thread / 32 ∧ input.key = record.key ∧ input.generation = record.generation := by
  obtain ⟨_,peer,input,hi,hs⟩ := hd origin record hr
  exact ⟨peer,input,hi,hs.1.1,hs.1.2,hs.2.2.2.1,hs.2.2.2.2⟩

theorem view_thread_ids (candidate : Candidate) : (candidate.view.traces.map Event.ThreadTrace.id) = candidate.traces.map ThreadTrace.id := by
  simp only [Candidate.view,List.map_map]
  rfl

theorem view_complete {candidate : Candidate} (hc : Complete candidate) : candidate.view.Complete := by
  intro trace ht
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp ht
  exact hc original ho

def Triple (code : List Instr) (pre : Scalar.Launch → Prop) (domain : Scalar.Launch → List Location)
    (post : Scalar.Launch → Scalar.ByteMap → Prop) : Prop :=
  ∀ launch candidate rf co observation, pre launch → WellFormed code launch candidate → Complete candidate →
    ControlAdmitted launch.geometry.block candidate →
    Defined launch.geometry.block candidate → Agreement launch.geometry.block candidate →
    Event.GenericMemoryConditions candidate.view launch.initial rf co →
    Event.ObserverConditions candidate.view launch.initial rf co observation → observation.domain = domain launch → post launch observation.output

/-- A verification client must establish this separately, rather than treating
undefined shuffle behavior as a successful kernel proof. -/
def Safe (code : List Instr) (pre : Scalar.Launch → Prop) : Prop :=
  ∀ launch candidate rf co, pre launch → WellFormed code launch candidate → Complete candidate →
    ControlAdmitted launch.geometry.block candidate →
    Agreement launch.geometry.block candidate → Event.GenericMemoryConditions candidate.view launch.initial rf co → Defined launch.geometry.block candidate

def Nonvacuous (code : List Instr) (pre : Scalar.Launch → Prop) (domain : Scalar.Launch → List Location) : Prop :=
  ∀ launch, pre launch → ∃ candidate rf co observation, WellFormed code launch candidate ∧ Complete candidate ∧
    ControlAdmitted launch.geometry.block candidate ∧
    Defined launch.geometry.block candidate ∧ Agreement launch.geometry.block candidate ∧
    Event.GenericMemoryConditions candidate.view launch.initial rf co ∧ Event.ObserverConditions candidate.view launch.initial rf co observation ∧ observation.domain = domain launch

end
end Ptx.Shuffle
