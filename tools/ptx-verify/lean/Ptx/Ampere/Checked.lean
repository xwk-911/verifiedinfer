import Ptx.Ampere.Origins
import Ptx.Ampere.Memory
import Ptx.Ampere.MmaProtocol

/-! Source-aware admission for the current non-bulk generic-proxy fragment.
Barrier matching uses actual PCs and all launched traces. Exited peers require
acyclic control order, including async base edges and MMA rendezvous; exit is not copy completion.
Physical storage, full SIMT/ISA UB and runtime correspondence remain separate.
-/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

def ThreadTrace.ExitedBeforeGeneration (t : ThreadTrace) (id generation : Nat) : Prop :=
  t.final.scalar.core.thread.status = .done ∧
  ∀ g, Event.ordinary (.barrierArrival id g) ∈ t.events → g < generation

def BarrierParticipation (c : Candidate) : Prop :=
  ∀ leave id generation, c.eventAt leave = some (.ordinary (.barrierReturn id generation)) →
    (∃ arrive, arrive.thread = leave.thread ∧ arrive.serial < leave.serial ∧
      c.eventAt arrive = some (.ordinary (.barrierArrival id generation))) ∧
    (∀ t ∈ c.traces, t.id.cta = leave.thread.cta →
      Event.ordinary (.barrierArrival id generation) ∈ t.events ∨ t.ExitedBeforeGeneration id generation)

def ExitBeforeReturn (c : Candidate) : Node → Node → Prop
  | .thread a,.thread b => c.Present (.thread a) ∧ ∃ t ∈ c.traces,
      t.id = a.thread ∧ t.id.cta = b.thread.cta ∧ ∃ id generation,
      c.eventAt b = some (.ordinary (.barrierReturn id generation)) ∧ t.ExitedBeforeGeneration id generation
  | _,_ => False

def ControlEdge (c : Candidate) (a b : Node) : Prop := BaseEdge c a b ∨ ExitBeforeReturn c a b ∨ MmaControl c a b
def ControlAcyclic (c : Candidate) : Prop := ∀ node, ¬ Ptx.Event.Path (ControlEdge c) node node

theorem control_acyclic_of_rank {c : Candidate} (rank : Node → Nat)
    (hb : ∀ a b, BaseEdge c a b → rank a < rank b)
    (he : ∀ a b, ExitBeforeReturn c a b → rank a < rank b)
    (hm : ∀ a b, MmaControl c a b → rank a < rank b) : ControlAcyclic c := by
  intro node hp
  exact Nat.lt_irrefl _ (hp.rank_lt rank (fun a b h => h.elim (hb a b) (fun h => h.elim (he a b) (hm a b))))

theorem control_implies_base_acyclic {c : Candidate} (hc : ControlAcyclic c) :
    MemoryGraph.BaseAcyclic c.memoryGraph := by
  intro node hp
  exact hc node (hp.mono (fun _ _ h => .inl h))

structure CheckedConditions (code : List Instr) (launch : Scalar.Launch) (c : Candidate)
    (rf : ReadsFrom) (co : Coherence) : Prop where
  provenance : WellFormed code launch c
  barrierSources : SourceAligned code launch c
  barriers : BarrierParticipation c
  control : ControlAcyclic c
  memory : MemoryConstraints c launch.initial rf co
  mma : MmaConditions code launch c

theorem checked_of_unique_sites {code launch c rf co}
    (hw : WellFormed code launch c) (hu : uniqueBarrierSites code = true)
    (hp : BarrierParticipation c) (hx : ControlAcyclic c)
    (hm : MemoryConstraints c launch.initial rf co) (hmm : MmaConditions code launch c) : CheckedConditions code launch c rf co :=
  ⟨hw,aligned_of_unique_sites hw hu,hp,hx,hm,hmm⟩

def CheckedTriple (code : List Instr) (pre : Scalar.Launch → Prop)
    (domain : Scalar.Launch → List Location) (post : Scalar.Launch → Ptx.Event.ByteMap Symbolic.Byte → Prop) : Prop :=
  ∀ launch c rf co o, pre launch → CheckedConditions code launch c rf co →
    ObserverConstraints c launch.initial rf co o → o.domain = domain launch → post launch o.output

def CheckedNonvacuous (code : List Instr) (pre : Scalar.Launch → Prop)
    (domain : Scalar.Launch → List Location) : Prop :=
  ∀ launch, pre launch → ∃ c rf co o, CheckedConditions code launch c rf co ∧
    ObserverConstraints c launch.initial rf co o ∧ o.domain = domain launch

end
end Ptx.Ampere
