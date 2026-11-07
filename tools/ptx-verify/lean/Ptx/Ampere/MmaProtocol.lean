import Ptx.Ampere.Origins

/-! Full-warp, source-aware matching and arithmetic for the fixed MMA form.
The participants are actual emitted entry/return events. In particular neither
a single thread's oracle nor an external matrix supplied as input is a witness.
MMA rendezvous edges constrain control order only; they do not publish memory.
-/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

structure MmaParticipant where
  entry : Ptx.Event.EventId
  leave : Ptx.Event.EventId
  call : MmaCall

def MmaParticipant.Valid (p : MmaParticipant) (code : List Instr) (launch : Scalar.Launch) (c : Candidate) : Prop :=
  p.entry.thread = p.leave.thread ∧ p.entry.serial < p.leave.serial ∧
  c.eventAt p.entry = some (.mmaEntry p.call) ∧ c.eventAt p.leave = some (.mmaReturn p.call) ∧
  sourcePC c code launch.params launch.geometry.block p.entry = some p.call.pc ∧
  sourcePC c code launch.params launch.geometry.block p.leave = some p.call.pc ∧
  let index := linearThread {id := p.leave.thread,params := launch.params,block := launch.geometry.block}
  p.call.warp = index/32 ∧ p.call.lane.val = index%32

def MmaConditions (code : List Instr) (launch : Scalar.Launch) (c : Candidate) : Prop :=
  ∀ event call, c.eventAt event = some (.mmaReturn call) →
    ∃ members : Mma.Lane → MmaParticipant,
      (members call.lane).leave = event ∧ (members call.lane).call = call ∧
      (∀ lane, (members lane).Valid code launch c ∧ (members lane).call.lane = lane ∧
        (members lane).leave.thread.cta = event.thread.cta ∧
        (members lane).call.warp = call.warp ∧ (members lane).call.ordinal = call.ordinal ∧ (members lane).call.pc = call.pc) ∧
      ∀ lane slot, (members lane).call.output slot =
        Mma.packedResults (fun p => (members p.1).call.inputs.a p.2)
          (fun p => (members p.1).call.inputs.b p.2) (fun p => (members p.1).call.inputs.c p.2) (lane,slot)

theorem mma_conditions_of_no_code {code launch c}
    (hw : WellFormed code launch c) (hn : noMmaCode code = true) : MmaConditions code launch c := by
  intro event call he
  exact (no_mma_returns_of_code hw hn event call he).elim

/-- Warp rendezvous is control dependence, not a memory fence. -/
def MmaControl (c : Candidate) : Node → Node → Prop
  | .thread entry,.thread leave => entry.thread.cta = leave.thread.cta ∧
      ∃ arriving returning, c.eventAt entry = some (.mmaEntry arriving) ∧
        c.eventAt leave = some (.mmaReturn returning) ∧
        arriving.warp = returning.warp ∧ arriving.ordinal = returning.ordinal ∧ arriving.pc = returning.pc
  | _,_ => False

def NoMmaReturns (c : Candidate) : Prop := ∀ event call, c.eventAt event ≠ some (.mmaReturn call)

def noMmaReturnEvents (events : List Event) : Bool :=
  events.all (fun e => match e with | .mmaReturn _ => false | _ => true)

theorem no_mma_returns_of_events {c : Candidate}
    (hn : ∀ t ∈ c.traces, noMmaReturnEvents t.events = true) : NoMmaReturns c := by
  intro event call he
  obtain ⟨t,ht,_,hi⟩ := eventAt_trace he
  have hh := List.all_eq_true.mp (hn t ht) (.mmaReturn call) (List.mem_of_getElem? hi)
  cases hh

theorem no_mma_control_of_no_returns {c : Candidate} (hn : NoMmaReturns c) (a b : Node) : ¬ MmaControl c a b := by
  cases a <;> cases b <;> try exact id
  rintro ⟨_,arriving,returning,_,he,_⟩
  exact hn _ _ he

theorem no_mma_control_of_no_code {code launch c} (hw : WellFormed code launch c) (hn : noMmaCode code = true)
    (a b : Node) : ¬ MmaControl c a b :=
  no_mma_control_of_no_returns (no_mma_returns_of_code hw hn) a b

end
end Ptx.Ampere
