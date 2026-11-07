import Ptx.Event.Memory

/-! Ordinary generic-proxy program order, full-CTA barrier synchronization and
their strict transitive closure. No async operations or proxy fences are accepted
by this layer. Barrier participation is checked separately from synchronization.
-/
namespace Ptx.Event
open Ptx.ISA

variable {ByteValue Answers : Type}

def Candidate.Present (c : Candidate ByteValue Answers) (id : EventId) : Prop := (c.eventAt id).isSome = true

def ProgramOrder (c : Candidate ByteValue Answers) (a b : EventId) : Prop :=
  c.Present a ∧ c.Present b ∧ a.thread = b.thread ∧ a.serial < b.serial

def BarrierSync (c : Candidate ByteValue Answers) (a b : EventId) : Prop :=
  a.thread.cta = b.thread.cta ∧ ∃ id generation,
    c.eventAt a = some (.barrierArrival id generation) ∧
    c.eventAt b = some (.barrierReturn id generation)

inductive Path (edge : α → α → Prop) : α → α → Prop
  | single {a b} : edge a b → Path edge a b
  | trans {a b c} : Path edge a b → Path edge b c → Path edge a c

theorem Path.mono {r s : α → α → Prop} (h : ∀ a b, r a b → s a b)
    {a b} (hp : Path r a b) : Path s a b := by
  induction hp with
  | single he => exact .single (h _ _ he)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Path.impossible {r : α → α → Prop} (h : ∀ a b, ¬ r a b)
    {a b} (hp : Path r a b) : False := by
  induction hp with
  | single he => exact h _ _ he
  | trans _ _ ih _ => exact ih

/-- Ranking is a proof aid for individual witnesses, not a restriction that
forces PTX executions to have a sequential memory schedule. -/
theorem Path.rank_lt {r : α → α → Prop} (rank : α → Nat)
    (h : ∀ a b, r a b → rank a < rank b) {a b} (hp : Path r a b) : rank a < rank b := by
  induction hp with
  | single he => exact h _ _ he
  | trans _ _ ih₁ ih₂ => omega

def BaseCausality (c : Candidate ByteValue Answers) : EventId → EventId → Prop :=
  Path (fun a b => ProgramOrder c a b ∨ BarrierSync c a b)

def BaseAcyclic (c : Candidate ByteValue Answers) : Prop := ∀ id, ¬ BaseCausality c id id

theorem program_causal {c : Candidate ByteValue Answers} {a b} (h : ProgramOrder c a b) : BaseCausality c a b :=
  .single (.inl h)

theorem barrier_causal {c : Candidate ByteValue Answers} {a b} (h : BarrierSync c a b) : BaseCausality c a b :=
  .single (.inr h)

theorem publish_across_barrier {c : Candidate ByteValue Answers} {write arrive leave read}
    (hw : ProgramOrder c write arrive) (hs : BarrierSync c arrive leave)
    (hr : ProgramOrder c leave read) : BaseCausality c write read :=
  .trans (program_causal hw) (.trans (barrier_causal hs) (program_causal hr))

/-- Exited threads may be exempt only when they did not participate in this or
any later generation of this resource. The current candidate abstraction does
not track exit-before-return timing; this predicate does not claim progress. -/
def ThreadTrace.ExitedBeforeGeneration (t : ThreadTrace ByteValue Answers) (id generation : Nat) : Prop :=
  t.final.thread.status = .done ∧
  ∀ g, Kind.barrierArrival id g ∈ t.events → g < generation

def BarrierParticipation (c : Candidate ByteValue Answers) : Prop :=
  ∀ leave id generation, c.eventAt leave = some (.barrierReturn id generation) →
    (∃ arrive, arrive.thread = leave.thread ∧ arrive.serial < leave.serial ∧
      c.eventAt arrive = some (.barrierArrival id generation)) ∧
    (∀ t ∈ c.traces, t.id.cta = leave.thread.cta →
      Kind.barrierArrival id generation ∈ t.events ∨ t.ExitedBeforeGeneration id generation)

/-- Exempting an exited peer requires its prior operations to be before this
return in execution control order. Without this obligation, two threads waiting
on different barriers could each justify returning by claiming the other exited.
These are CONTROL edges, not memory synchronization/visibility guarantees. -/
def ExitBeforeReturn (c : Candidate ByteValue Answers) (a b : EventId) : Prop :=
  c.Present a ∧ ∃ t ∈ c.traces, t.id = a.thread ∧ t.id.cta = b.thread.cta ∧
    ∃ id generation, c.eventAt b = some (.barrierReturn id generation) ∧
      t.ExitedBeforeGeneration id generation

def BarrierControlAcyclic (c : Candidate ByteValue Answers) : Prop :=
  ∀ id, ¬ Path (fun a b => ProgramOrder c a b ∨ BarrierSync c a b ∨ ExitBeforeReturn c a b) id id

theorem barrier_control_of_no_returns {c : Candidate ByteValue Answers} (hb : BaseAcyclic c)
    (hn : ∀ leave id generation, c.eventAt leave ≠ some (.barrierReturn id generation)) :
    BarrierControlAcyclic c := by
  intro id hp
  apply hb id
  apply hp.mono
  intro a b he
  rcases he with hpo | hsync | hexit
  · exact .inl hpo
  · exact .inr hsync
  · obtain ⟨_, t, _, _, _, bid, generation, hret, _⟩ := hexit
    exact (hn b bid generation hret).elim

end Ptx.Event
