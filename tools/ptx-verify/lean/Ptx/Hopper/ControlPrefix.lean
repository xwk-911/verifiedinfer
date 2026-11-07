import Ptx.Hopper.UnifiedControl

/-! Finite event-by-event prefixes of the existing unified control graph.
Each advance adds one actual node with every control predecessor already seen.
This is an access-order interpretation, not a physical GPU scheduler, memory
value microstep model or CUDA runtime refinement. -/
namespace Ptx.Hopper.Progress
open Ptx.ISA
noncomputable section

abbrev Cut := Unified.ControlNode → Prop

def Present (candidate : Unified.Candidate) : Unified.ControlNode → Prop
  | .base node => Tma.Present candidate.view node
  | .arrival event => (candidate.nativeSignatureAt event).isSome = true
  | .operand issue _ => (candidate.representativeAt issue).isSome = true

def Closed (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry) (done : Cut) : Prop :=
  ∀ before after, Unified.ControlEdge block candidate histories before after → done after → done before

def Valid (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry) (done : Cut) : Prop :=
  Closed block candidate histories done ∧ ∀ node, done node → Present candidate node

inductive Advance (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry) : Cut → Cut → Prop
  | next {done : Cut} (node : Unified.ControlNode)
      (actual : Present candidate node) (fresh : ¬done node)
      (predecessors : ∀ before, Unified.ControlEdge block candidate histories before node → done before) :
      Advance block candidate histories done (fun n => done n ∨ n = node)

inductive Reached (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry) : Cut → Prop
  | empty : Reached block candidate histories (fun _ => False)
  | next {before after} : Reached block candidate histories before → Advance block candidate histories before after →
      Reached block candidate histories after

theorem closed_path {block candidate histories done before after}
    (hc : Closed block candidate histories done)
    (hp : Ptx.Event.Path (Unified.ControlEdge block candidate histories) before after) (hd : done after) : done before := by
  induction hp with
  | single he => exact hc _ _ he hd
  | trans first rest ihfirst ihrest => exact ihfirst (ihrest hd)

theorem advance_monotone {block candidate histories before after}
    (hs : Advance block candidate histories before after) : ∀ node, before node → after node := by
  cases hs
  exact fun _ h => Or.inl h

theorem advance_valid {block candidate histories before after}
    (hv : Valid block candidate histories before) (hs : Advance block candidate histories before after) : Valid block candidate histories after := by
  cases hs with
  | next node actual fresh predecessors =>
    constructor
    · intro left right he hd
      rcases hd with hd | rfl
      · exact Or.inl (hv.1 _ _ he hd)
      · exact Or.inl (predecessors left he)
    · intro n hn
      rcases hn with hn | rfl
      · exact hv.2 n hn
      · exact actual

theorem reached_valid {block candidate histories done} (hr : Reached block candidate histories done) : Valid block candidate histories done := by
  induction hr with
  | empty => exact ⟨fun _ _ _ h => h.elim,fun _ h => h.elim⟩
  | next before step ih => exact advance_valid ih step

theorem reached_finite {block candidate histories done} (hr : Reached block candidate histories done) :
    ∃ nodes : List Unified.ControlNode, ∀ node, done node ↔ node ∈ nodes := by
  induction hr with
  | empty => exact ⟨[],by simp⟩
  | next before step ih =>
    obtain ⟨nodes,hn⟩ := ih
    cases step with
    | next node actual fresh predecessors =>
      refine ⟨node::nodes,?_⟩
      intro n
      simp only [List.mem_cons,← hn]
      exact or_comm

theorem rank_cut_closed {block candidate histories} (rank : Unified.ControlNode → Nat)
    (hr : ∀ before after, Unified.ControlEdge block candidate histories before after → rank before < rank after) (limit : Nat) :
    Closed block candidate histories (fun node => rank node < limit) := by
  intro before after he hd
  exact (hr before after he).trans hd

end
end Ptx.Hopper.Progress
