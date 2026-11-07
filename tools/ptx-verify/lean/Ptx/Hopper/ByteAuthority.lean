import Ptx.Hopper.KernelUse
import Iris.BI.Lib.GenHeap
import Mathlib.Data.Nat.Pairing

/-! Active access authority indexed by actual byte locations, separate from
queued lifetime reservations and memory values. The conservative baseline grants
exclusive authority, including for reads. It refines the existing source/control
prefix: a node can retire only when all its actual ordinary/async/resource byte
uses are held. This is not a CUDA allocation or weak-memory value simulation.
-/
namespace Ptx.Hopper.ByteAuthority
open Ptx.ISA Ptx.Hopper.Progress
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

abbrev Key := Nat
abbrev HeapF (V : Type) := _root_.Std.ExtTreeMap Key V compare
local instance : Iris.Std.LawfulPartialMap HeapF Key :=
  (inferInstance : Iris.Std.LawfulFiniteMap HeapF Key).toLawfulPartialMap
local instance : Iris.Std.PartialMap HeapF Key :=
  (inferInstance : Iris.Std.LawfulFiniteMap HeapF Key).toLawfulPartialMap.toPartialMap

def key (loc : Location) : Key := match loc.space with
  | .global => Nat.pair 0 loc.address + 1
  | .shared cta => Nat.pair (Nat.pair cta.x (Nat.pair cta.y cta.z)+1) loc.address + 1
def controlKey : Key := 0

theorem key_injective : Function.Injective key := by
  intro a b he
  cases a with | mk sa aa =>
    cases b with | mk sb ab =>
      cases sa with
      | global =>
        cases sb with
        | global => simp only [key,Nat.add_right_cancel_iff,Nat.pair_eq_pair] at he; simp [he.2]
        | shared cta => simp only [key,Nat.add_right_cancel_iff,Nat.pair_eq_pair] at he; omega
      | shared ca =>
        cases sb with
        | global => simp only [key,Nat.add_right_cancel_iff,Nat.pair_eq_pair] at he; omega
        | shared cb =>
          cases ca; cases cb
          simp only [key,Nat.add_right_cancel_iff,Nat.pair_eq_pair] at he
          rcases he with ⟨⟨hx,hy,hz⟩,ha⟩
          subst_vars
          rfl

theorem byte_key_not_control (loc : Location) : key loc ≠ controlKey := by
  cases loc with
  | mk space address => cases space <;> simp [key,controlKey]

inductive Owner
  | available
  | held (control : Unified.ControlNode) (mode : Ptx.Async.Mode)
  deriving Repr, DecidableEq

structure State where
  coupled : Bridge.State
  bytes : HeapF Owner

def Uses (candidate : Unified.Candidate) (node : Unified.ControlNode) (loc : Location) (mode : Ptx.Async.Mode) : Prop :=
  ∃ work, Progress.UnifiedUse Tma.localShared Access.globalDescriptor candidate work node loc mode

def Ready (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry) (done : Cut)
    (node : Unified.ControlNode) : Prop :=
  Present candidate node ∧ ¬done node ∧ ∀ before, Unified.ControlEdge block candidate histories before node → done before

/-- Full write authority also discharges a read demand, as required by RMW.
Source use modes and the public claim's source check remain exact. -/
def Authorizes (granted requested : Ptx.Async.Mode) : Prop := granted = .write ∨ granted = requested

theorem authorizes_self (mode : Ptx.Async.Mode) : Authorizes mode mode := Or.inr rfl
theorem write_authorizes (mode : Ptx.Async.Mode) : Authorizes .write mode := Or.inl rfl
theorem read_cannot_authorize_write : ¬Authorizes .read .write := by simp [Authorizes]

def AllHeld (candidate : Unified.Candidate) (state : State) (node : Unified.ControlNode) : Prop :=
  ∀ loc mode, Uses candidate node loc mode → ∃ granted,
    get? state.bytes (key loc) = some (.held node granted) ∧ Authorizes granted mode

inductive Error
  | unready | uncovered | unavailable
  | incompleteWork
  | protocolFailure (error : Ptx.Async.Error)
  deriving Repr, DecidableEq
structure Claim where
  node : Unified.ControlNode
  location : Location
  mode : Ptx.Async.Mode
  deriving Repr, DecidableEq

noncomputable def claim (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (request : Claim) (state : State) : Except Error State := by
  classical
  exact if Ready block candidate histories state.coupled.done request.node then
    if Uses candidate request.node request.location request.mode then
      match get? state.bytes (key request.location) with
      | some .available => .ok {state with bytes := insert state.bytes (key request.location) (.held request.node request.mode)}
      | _ => .error .unavailable
    else .error .uncovered
  else .error .unready

theorem claim_succeeds {block candidate histories request state}
    (hr : Ready block candidate histories state.coupled.done request.node)
    (hu : Uses candidate request.node request.location request.mode)
    (hb : get? state.bytes (key request.location) = some .available) :
    claim block candidate histories request state = .ok {state with bytes := insert state.bytes (key request.location) (.held request.node request.mode)} := by
  simp [claim,hr,hu,hb]

theorem claim_spec {block candidate histories request state next}
    (hs : claim block candidate histories request state = .ok next) :
    Ready block candidate histories state.coupled.done request.node ∧ Uses candidate request.node request.location request.mode ∧
    get? state.bytes (key request.location) = some .available ∧
    next = {state with bytes := insert state.bytes (key request.location) (.held request.node request.mode)} := by
  unfold claim at hs
  split at hs
  · rename_i hr
    split at hs
    · rename_i hu
      split at hs
      · rename_i hb; exact ⟨hr,hu,hb,Except.ok.inj hs.symm⟩
      · cases hs
    · cases hs
  · cases hs

theorem claim_done_rejected {block candidate histories request state}
    (hd : state.coupled.done request.node) : claim block candidate histories request state = .error .unready := by
  have hn : ¬Ready block candidate histories state.coupled.done request.node := fun hr => hr.2.1 hd
  simp [claim,hn]

theorem claim_unavailable {block candidate histories request state}
    (hr : Ready block candidate histories state.coupled.done request.node) (hu : Uses candidate request.node request.location request.mode)
    (hb : get? state.bytes (key request.location) ≠ some .available) :
    claim block candidate histories request state = .error .unavailable := by
  unfold claim
  simp only [hr,hu,ite_true]

theorem claim_other_byte_preserved {block candidate histories request state next other}
    (hs : claim block candidate histories request state = .ok next) (hne : request.location ≠ other) :
    get? next.bytes (key other) = get? state.bytes (key other) := by
  rw [(claim_spec hs).2.2.2]
  exact get?_insert_ne (fun he => hne (key_injective he))

theorem ready_at_rank_cut {block resolve candidate histories node}
    (hh : ∀ loc, Tma.HistoryValid resolve candidate.view loc (histories loc))
    (rank : Unified.ControlNode → Nat)
    (hr : ∀ before after, Unified.ControlEdge block candidate histories before after → rank before < rank after)
    (hp : Present candidate node) :
    Ready block candidate histories (fun n => Present candidate n ∧ rank n < rank node) node := by
  refine ⟨hp,by simp,?_⟩
  intro before he
  exact ⟨(Ptx.Hopper.Progress.control_edge_present hh he).1,hr before node he⟩

def release (node : Unified.ControlNode) (owner : Owner) : Owner :=
  match owner with | .held actual _ => if actual = node then .available else owner | .available => .available

def retired (state : State) (node : Unified.ControlNode) : State :=
  ⟨⟨state.coupled.protocol,fun n => state.coupled.done n ∨ n = node⟩,Iris.Std.PartialMap.map (release node) state.bytes⟩

inductive Step (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (cluster : Access.ClusterScope) (plan : Bridge.Plan) : State → State → Prop
  | claim {state next request} (hs : claim block candidate histories request state = .ok next) :
      Step block candidate histories cluster plan state next
  | retire {state node} (hr : Ready block candidate histories state.coupled.done node) (ha : AllHeld candidate state node) :
      Step block candidate histories cluster plan state (retired state node)
  | protocol {state next} (hs : Bridge.Step block Tma.localShared candidate histories cluster plan state.coupled next)
      (stable : state.coupled.done = next.done) :
      Step block candidate histories cluster plan state {state with coupled := next}

theorem claim_preserves_coupled {block candidate histories request state next}
    (hs : claim block candidate histories request state = .ok next) : next.coupled = state.coupled := by
  rw [(claim_spec hs).2.2.2]

theorem retire_projects {block candidate histories cluster plan state node}
    (hr : Ready block candidate histories state.coupled.done node) :
    Bridge.Step block Tma.localShared candidate histories cluster plan state.coupled (retired state node).coupled :=
  .access (.next node hr.1 hr.2.1 hr.2.2)

theorem retire_requires_actual_byte {candidate state node loc mode}
    (ha : AllHeld candidate state node) (hu : Uses candidate node loc mode) :
    ∃ granted, get? state.bytes (key loc) = some (.held node granted) ∧ Authorizes granted mode := ha loc mode hu

theorem retire_returns_actual_byte {candidate state node loc mode}
    (ha : AllHeld candidate state node) (hu : Uses candidate node loc mode) :
    get? (retired state node).bytes (key loc) = some .available := by
  obtain ⟨granted,hheld,_⟩ := ha loc mode hu
  simp [retired,get?_map,hheld,release]

end
end Ptx.Hopper.ByteAuthority
