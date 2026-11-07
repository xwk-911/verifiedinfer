import Ptx.Ampere.Source
import Ptx.MemoryGraph.ObservationWitness

/-! The generic-proxy memory fragment over actual Ampere candidate nodes.
This adapter does not by itself admit an execution: source production, barrier
participation/control and launch/storage validity remain separate obligations.
Copy payload agreement is checked at the independent read node. A copy does
not become a scalar store in issuer program order.
-/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

def Node.agent : Node → MemoryGraph.Agent
  | .thread event => .thread event.thread
  | .copyRead operation | .copyWrite operation => .operation operation.thread 0 operation.ordinal

def Candidate.memoryGraph (c : Candidate) : MemoryGraph.Graph Node Symbolic.Byte := {
  kind := c.memoryKind
  present := c.Present
  agent := Node.agent
  po := ProgramOrder c
  base := BaseOrder c
  complete := Complete c
}

abbrev MemorySource := Option Node
abbrev ReadsFrom := MemoryGraph.ReadsFrom Node MemorySource
abbrev Coherence := MemoryGraph.Coherence MemorySource
abbrev Observation := MemoryGraph.Observation Symbolic.Byte MemorySource
abbrev MemoryConstraints (c : Candidate) (initial : Ptx.Event.ByteMap Symbolic.Byte)
    (rf : ReadsFrom) (co : Coherence) := MemoryGraph.MemoryConditions c.memoryGraph initial rf co
abbrev ObserverConstraints (c : Candidate) (initial : Ptx.Event.ByteMap Symbolic.Byte)
    (rf : ReadsFrom) (co : Coherence) (o : Observation) := MemoryGraph.ObserverConditions c.memoryGraph initial rf co o

@[simp] theorem graph_readByte (c : Candidate) (node loc) :
    c.memoryGraph.readByte node loc = c.readByte node loc := rfl
@[simp] theorem graph_writeByte (c : Candidate) (node loc) :
    c.memoryGraph.writeByte node loc = c.writeByte node loc := rfl

/-- Source metadata can differ on unused oracle replies. The augmented memory
view is determined by actual events, recorded copies and source completion. -/
theorem memoryGraph_eq {c d : Candidate}
    (he : c.eventAt = d.eventAt) (hc : c.copyAt = d.copyAt) (hd : Complete c ↔ Complete d) :
    c.memoryGraph = d.memoryGraph := by
  have hk : c.memoryKind = d.memoryKind := by
    funext node
    cases node <;> simp only [Candidate.memoryKind,he,hc]
  have hp : c.Present = d.Present := by
    funext node
    cases node <;> simp only [Candidate.Present,he,hc]
  have hpo : ProgramOrder c = ProgramOrder d := by
    funext a b
    cases a <;> cases b <;> simp only [ProgramOrder,hp]
  have hb : BaseEdge c = BaseEdge d := by
    funext a b
    cases a <;> cases b <;>
      simp only [BaseEdge,hpo,BarrierSync,IssueBefore,CopyInternal,Completion,WaitCovers,he,hc,hp]
  simp only [Candidate.memoryGraph,hk,hp,hpo,BaseOrder,hb,propext hd]

theorem copy_read_agent_differs_from_issuer (operation : CopyId) (serial : Nat) :
    Node.agent (.copyRead operation) ≠ Node.agent (.thread ⟨operation.thread,serial⟩) := by
  simp [Node.agent]
theorem copy_write_agent_differs_from_issuer (operation : CopyId) (serial : Nat) :
    Node.agent (.copyWrite operation) ≠ Node.agent (.thread ⟨operation.thread,serial⟩) := by
  simp [Node.agent]
theorem different_copy_agents {a b : CopyId} (hn : a ≠ b) :
    Node.agent (.copyWrite a) ≠ Node.agent (.copyWrite b) := by
  rcases a with ⟨ta,na⟩
  rcases b with ⟨tb,nb⟩
  simpa [Node.agent,CopyId.mk.injEq] using hn

theorem copy_read_not_rmw (c : Candidate) (operation : CopyId) :
    ¬ c.memoryGraph.IsRMW (.copyRead operation) := by
  rintro ⟨scope,base,bytes,he⟩
  change ((c.copyAt operation).map (fun op => Ptx.Event.Kind.read op.src op.bytes)) = _ at he
  cases hc : c.copyAt operation <;> simp [hc] at he
theorem copy_write_not_rmw (c : Candidate) (operation : CopyId) :
    ¬ c.memoryGraph.IsRMW (.copyWrite operation) := by
  rintro ⟨scope,base,bytes,he⟩
  change ((c.copyAt operation).map (fun op => Ptx.Event.Kind.write op.dst op.bytes)) = _ at he
  cases hc : c.copyAt operation <;> simp [hc] at he

/-- Sharing an issuer does not make a scalar access and an async write morally
strong. Publication must be established through completion and base causality. -/
theorem copy_write_not_strong_with_thread (c : Candidate) (operation : CopyId) (event : Ptx.Event.EventId) :
    ¬ MemoryGraph.MorallyStrong c.memoryGraph (.copyWrite operation) (.thread event) := by
  rw [MemoryGraph.morally_strong_of_no_rmw (copy_write_not_rmw c operation)]
  rintro ⟨he,_⟩
  cases he

theorem waited_copy_causality {c operation event read}
    (hw : WaitCovers c operation event)
    (hp : ProgramOrder c (.thread event) (.thread read))
    (ho : c.memoryGraph.Overlap (.copyWrite operation) (.thread read)) (rf : ReadsFrom) :
    MemoryGraph.Causality c.memoryGraph rf (.copyWrite operation) (.thread read) :=
  MemoryGraph.causal_of_base ho (.trans (completed_before_wait hw) (thread_program_causal hp))

/-- This reusable visibility rule quantifies over every rf/co satisfying the
memory fragment. Eligibility and unique writer are explicit proof obligations;
the rule does not assume the desired read value or a chosen scheduling order. -/
theorem waited_unique_copy_value {c : Candidate} {initial rf co operation wait read loc written observed}
    (hc : MemoryConstraints c initial rf co)
    (he : MemoryGraph.Eligible c.memoryGraph rf (.thread read) loc)
    (hw : c.writeByte (.copyWrite operation) loc = some written)
    (hr : c.readByte (.thread read) loc = some observed)
    (hwait : WaitCovers c operation wait)
    (hp : ProgramOrder c (.thread wait) (.thread read))
    (hu : ∀ other value, c.writeByte other loc = some value → other = .copyWrite operation) :
    observed = written := by
  apply MemoryGraph.unique_writer_visible (c := c.memoryGraph) (writer := .copyWrite operation) (read := .thread read) hc he hw hr
    (waited_copy_causality hwait hp ?_ rf) hu
  exact ⟨loc,Or.inr (by rw [graph_writeByte,hw]; rfl),Or.inl (by rw [graph_readByte,hr]; rfl)⟩

/-- Cooperative reads may belong to a different thread from the copy issuer.
Publication follows the actual wait and CTA barrier. Other phases must be
classified using the actual graph; repeated writes are allowed. -/
theorem published_phase_copy_source {c : Candidate} {initial rf co operation wait arrive leave read loc written observed}
    (hc : MemoryConstraints c initial rf co)
    (he : MemoryGraph.Eligible c.memoryGraph rf (.thread read) loc)
    (hw : c.writeByte (.copyWrite operation) loc = some written)
    (hr : c.readByte (.thread read) loc = some observed)
    (hwait : WaitCovers c operation wait)
    (ha : ProgramOrder c (.thread wait) (.thread arrive))
    (hb : BarrierSync c (.thread arrive) (.thread leave))
    (hl : ProgramOrder c (.thread leave) (.thread read))
    (hphase : ∀ other value, c.writeByte other loc = some value →
      other = .copyWrite operation ∨ MemoryGraph.Causality c.memoryGraph rf other (.copyWrite operation) ∨
        MemoryGraph.Causality c.memoryGraph rf (.thread read) other) :
    rf (.thread read) loc = MemoryGraph.writeSource (.copyWrite operation) := by
  refine MemoryGraph.phase_writer_source (c := c.memoryGraph) (rf := rf) (co := co)
    (writer := Node.copyWrite operation) (read := Node.thread read) (loc := loc)
    (vw := written) (vr := observed) hc he ?_ ?_ ?_ ?_
  · exact hw
  · exact hr
  · exact MemoryGraph.causal_of_base
      ⟨loc,Or.inr (by rw [graph_writeByte,hw]; rfl),Or.inl (by rw [graph_readByte,hr]; rfl)⟩
      (publish_after_wait_and_barrier hwait ha hb hl)
  · exact hphase

theorem published_phase_copy_value {c : Candidate} {initial rf co operation wait arrive leave read loc written observed}
    (hc : MemoryConstraints c initial rf co)
    (he : MemoryGraph.Eligible c.memoryGraph rf (.thread read) loc)
    (hw : c.writeByte (.copyWrite operation) loc = some written)
    (hr : c.readByte (.thread read) loc = some observed)
    (hwait : WaitCovers c operation wait)
    (ha : ProgramOrder c (.thread wait) (.thread arrive))
    (hb : BarrierSync c (.thread arrive) (.thread leave))
    (hl : ProgramOrder c (.thread leave) (.thread read))
    (hphase : ∀ other value, c.writeByte other loc = some value →
      other = .copyWrite operation ∨ MemoryGraph.Causality c.memoryGraph rf other (.copyWrite operation) ∨
        MemoryGraph.Causality c.memoryGraph rf (.thread read) other) : observed = written := by
  have hs := published_phase_copy_source hc he hw hr hwait ha hb hl hphase
  have hv := MemoryGraph.write_read_value hc.agreement he hr hs
  exact Option.some.inj (hv.symm.trans hw)

end
end Ptx.Ampere
