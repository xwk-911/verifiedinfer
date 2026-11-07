import Ptx.Hopper.ResourceHistory

/-! Control consistency of source/resource witnesses. Resource serialization is
not a memory publication edge. TMA proxy visibility and asynchronous operation
completion remain separate semantic obligations. -/
namespace Ptx.Hopper
open Ptx.ISA
noncomputable section

def ProgramOrder (c : Candidate) (a b : Ptx.Event.EventId) : Prop :=
  c.Present a ∧ c.Present b ∧ a.thread = b.thread ∧ a.serial < b.serial
instance (c a b) : Decidable (ProgramOrder c a b) := by unfold ProgramOrder; infer_instance

def Candidate.ctaTag (c : Candidate) (arrival : Bool) (id : Ptx.Event.EventId) : Option (Nat × Nat) :=
  (c.eventAt id).bind (fun e => match e with
    | .ampere (.ordinary (.barrierArrival bid generation)) => if arrival then some (bid,generation) else none
    | .ampere (.ordinary (.barrierReturn bid generation)) => if arrival then none else some (bid,generation)
    | _ => none)
def CTAControl (c : Candidate) (a b : Ptx.Event.EventId) : Prop :=
  match c.ctaTag true a,c.ctaTag false b with
  | some left,some right => a.thread.cta = b.thread.cta ∧ left = right
  | _,_ => False
instance (c a b) : Decidable (CTAControl c a b) := by unfold CTAControl; split <;> infer_instance

def ResourceEdge (c : Candidate) (histories : Location → List ResourceEntry) (a b : Ptx.Event.EventId) : Prop :=
  ∃ loc ∈ c.resourceLocations, HistoryBefore (histories loc) a b
instance (c histories a b) : Decidable (ResourceEdge c histories a b) := by unfold ResourceEdge; infer_instance

def ResourceControlEdge (c : Candidate) (histories : Location → List ResourceEntry) (a b : Ptx.Event.EventId) : Prop :=
  ProgramOrder c a b ∨ CTAControl c a b ∨ ResourceEdge c histories a b
instance (c histories a b) : Decidable (ResourceControlEdge c histories a b) := by unfold ResourceControlEdge; infer_instance

def ResourceControlAcyclic (c : Candidate) (histories : Location → List ResourceEntry) : Prop :=
  ∀ event, ¬ Ptx.Event.Path (ResourceControlEdge c histories) event event

structure ResourceConditions (code : List Instr) (launch : Scalar.Launch) (c : Candidate)
    (histories : Location → List ResourceEntry) : Prop where
  source : WellFormed code launch c
  complete : Complete c
  histories_valid : ∀ loc, HistoryValid c loc (histories loc)
  control : ResourceControlAcyclic c histories

theorem cta_tag_present {c : Candidate} {arrival id value} (he : c.ctaTag arrival id = some value) : c.Present id := by
  cases hh : c.eventAt id with
  | none => simp [Candidate.ctaTag,hh] at he
  | some e => simp [Candidate.Present,hh]

theorem cta_control_present {c a b} (he : CTAControl c a b) : c.Present a ∧ c.Present b := by
  unfold CTAControl at he
  cases ha : c.ctaTag true a <;> cases hb : c.ctaTag false b <;> simp only [ha,hb] at he
  exact ⟨cta_tag_present ha,cta_tag_present hb⟩

theorem control_edge_present {c histories a b}
    (h : ∀ loc, HistoryValid c loc (histories loc)) (he : ResourceControlEdge c histories a b) : c.Present a ∧ c.Present b := by
  rcases he with hp | hc | ⟨loc,_,hh⟩
  · exact ⟨hp.1,hp.2.1⟩
  · exact cta_control_present hc
  · exact history_before_present (h loc) hh

theorem resource_control_acyclic_of_rank {c histories}
    (h : ∀ loc, HistoryValid c loc (histories loc)) (rank : Ptx.Event.EventId → Nat)
    (hr : ∀ a ∈ c.eventIds, ∀ b ∈ c.eventIds, ResourceControlEdge c histories a b → rank a < rank b) :
    ResourceControlAcyclic c histories := by
  intro event hp
  have hh := hp.rank_lt rank (fun a b he => by
    have ha := control_edge_present h he
    exact hr a (present_mem_eventIds ha.1) b (present_mem_eventIds ha.2) he)
  omega

theorem resource_two_edge_cycle_rejected {c histories a b} (h : ResourceControlAcyclic c histories)
    (ha : ResourceControlEdge c histories a b) (hb : ResourceControlEdge c histories b a) : False :=
  h a (.trans (.single ha) (.single hb))

end
end Ptx.Hopper
