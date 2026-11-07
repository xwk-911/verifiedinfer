import Ptx.Hopper.TmaResources

/-! Control-only composition of source steps, CTA rendezvous, implicit TMA
accesses/completion and source-matched resource histories. This does not turn
control edges into cross-proxy memory publication. -/
namespace Ptx.Hopper.Tma
open Ptx.ISA
noncomputable section

def CTAControl (c : Candidate) : Node → Node → Prop
  | .source a,.source b => Hopper.CTAControl c a b
  | _,_ => False

def ResourceEdge (histories : Location → List Entry) (a b : Node) : Prop :=
  ∃ loc, ∃ left ∈ histories loc, ∃ right ∈ histories loc,
    Before (histories loc) left.origin right.origin ∧ left.origin.node = a ∧ right.origin.node = b

def ControlEdge (c : Candidate) (histories : Location → List Entry) (a b : Node) : Prop :=
  ProgramOrder c a b ∨ CTAControl c a b ∨ InternalEdge c a b ∨ ResourceEdge histories a b

def ControlAcyclic (c : Candidate) (histories : Location → List Entry) : Prop :=
  ∀ node, ¬ Ptx.Event.Path (ControlEdge c histories) node node

theorem control_acyclic_of_rank {c histories} (rank : Node → Nat)
    (hp : ∀ a b, ProgramOrder c a b → rank a < rank b)
    (hc : ∀ a b, CTAControl c a b → rank a < rank b)
    (hi : ∀ a b, InternalEdge c a b → rank a < rank b)
    (hr : ∀ a b, ResourceEdge histories a b → rank a < rank b) : ControlAcyclic c histories := by
  intro node path
  have hh := path.rank_lt rank (fun a b he => he.elim (hp a b) (fun h => h.elim (hc a b) (fun h => h.elim (hi a b) (hr a b))))
  omega

theorem read_has_copy {c id offset} (he : (readLocation c id offset).isSome = true) :
    ∃ copy, copyAt c id = some copy ∧ offset < copy.descriptor.bytes := by
  unfold readLocation at he
  cases hc : copyAt c id with
  | none => simp [hc] at he
  | some copy =>
    have hh : (sourceByte copy.descriptor copy.coordinates offset).isSome = true := by simpa [hc] using he
    obtain ⟨where_,hwhere⟩ := Option.isSome_iff_exists.mp hh
    refine ⟨copy,?_,(source_byte_some hwhere).1⟩
    first | rfl | exact hc

theorem write_has_copy {c id offset} (he : WritePresent c id offset) :
    ∃ copy, copyAt c id = some copy ∧ offset < copy.descriptor.bytes := by
  unfold WritePresent at he
  cases hc : copyAt c id with
  | none => simp [hc] at he
  | some copy =>
    refine ⟨copy,?_,?_⟩
    · first | rfl | exact hc
    · simpa [hc] using he

/-- TMA component evidence, not combined ordinary/TMA memory, rf/co/race,
observer, proxy or descriptor-encoding admission. -/
structure Components (code : List Instr) (launch : Scalar.Launch) (c : Candidate)
    (resolve : SharedResolver) (maps : Nat → Option Descriptor2D) (histories : Location → List Entry) : Prop where
  source : WellFormed code launch c
  complete : Complete c
  descriptors : DescriptorAgreement c maps
  payload : PayloadAgreement c launch.initial
  histories_valid : ∀ loc, HistoryValid resolve c loc (histories loc)
  control : ControlAcyclic c histories

end
end Ptx.Hopper.Tma
