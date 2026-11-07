import Ptx.Hopper.ByteAuthority
import Ptx.Hopper.PrefixExecution
import Ptx.Kernels.HopperDoubleBufferWholeInventory

/-! Active claims stay actual and pending; retirement is the sole source
advance and requires all actual bytes. Host/device actions preserve the cut.
-/
namespace Ptx.Hopper.ByteAuthority
open Ptx.ISA Ptx.Hopper.Progress
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
noncomputable section

def Active (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry) (state : State) : Prop :=
  ∀ loc node mode, get? state.bytes (key loc) = some (.held node mode) →
    Uses candidate node loc mode ∧ Ready block candidate histories state.coupled.done node

inductive Steps (block : Dim3) (candidate : Unified.Candidate) (histories : Location → List Tma.Entry)
    (cluster : Access.ClusterScope) (plan : Bridge.Plan) : State → State → Prop
  | refl (state) : Steps block candidate histories cluster plan state state
  | next {state mid last} : Step block candidate histories cluster plan state mid →
      Steps block candidate histories cluster plan mid last → Steps block candidate histories cluster plan state last

theorem step_projects {block candidate histories cluster plan state next}
    (hs : Step block candidate histories cluster plan state next) :
    Bridge.Steps block Tma.localShared candidate histories cluster plan state.coupled next.coupled := by
  cases hs with
  | claim hs => rw [claim_preserves_coupled hs]; exact .refl _
  | retire hr ha => exact .next (retire_projects hr) (.refl _)
  | protocol hs stable => exact .next hs (.refl _)

theorem steps_projects {block candidate histories cluster plan state last}
    (hs : Steps block candidate histories cluster plan state last) :
    Bridge.Steps block Tma.localShared candidate histories cluster plan state.coupled last.coupled := by
  induction hs with
  | refl => exact .refl _
  | next first rest ih => exact Bridge.steps_trans (step_projects first) ih

theorem advance_changes_cut {block candidate histories before after}
    (hs : Advance block candidate histories before after) : before ≠ after := by
  cases hs with
  | next node actual fresh predecessors =>
    intro heq
    exact fresh (Eq.mpr (congrFun heq node) (Or.inr rfl))

theorem claim_active {block candidate histories request state next}
    (hi : Active block candidate histories state)
    (hs : claim block candidate histories request state = .ok next) : Active block candidate histories next := by
  obtain ⟨hr,hu,hb,rfl⟩ := claim_spec hs
  intro loc node mode hh
  by_cases he : key request.location = key loc
  · have hl := key_injective he
    subst loc
    simp only [get?_insert] at hh
    cases hh
    exact ⟨hu,hr⟩
  · have hold : get? state.bytes (key loc) = some (.held node mode) := by
      simpa only [get?_insert_ne he] using hh
    exact hi loc node mode hold

theorem retire_active {block candidate histories state node}
    (hi : Active block candidate histories state) : Active block candidate histories (retired state node) := by
  intro loc other mode hh
  change get? (Iris.Std.PartialMap.map (release node) state.bytes) (key loc) = some (.held other mode) at hh
  rw [get?_map] at hh
  cases ho : get? state.bytes (key loc) with
  | none => simp [ho] at hh
  | some owner =>
    cases owner with
    | available => simp [ho,release] at hh
    | held control kind =>
      by_cases he : control = node
      · simp [ho,release,he] at hh
      · simp only [ho,Option.map_some,release,he,ite_false,Option.some.injEq,Owner.held.injEq] at hh
        rcases hh with ⟨rfl,rfl⟩
        obtain ⟨hu,hr⟩ := hi loc control kind ho
        refine ⟨hu,hr.1,?_,?_⟩
        · intro hd
          rcases hd with hd | heq
          · exact hr.2.1 hd
          · exact he heq
        · intro before hbefore
          exact Or.inl (hr.2.2 before hbefore)

theorem step_active {block candidate histories cluster plan state next}
    (hi : Active block candidate histories state) (hs : Step block candidate histories cluster plan state next) :
    Active block candidate histories next := by
  cases hs with
  | claim hs => exact claim_active hi hs
  | retire hr ha => exact retire_active hi
  | protocol hs stable =>
    intro loc node mode hh
    obtain ⟨hu,hr⟩ := hi loc node mode hh
    exact ⟨hu,by simpa only [stable] using hr⟩

theorem steps_active {block candidate histories cluster plan state next}
    (hi : Active block candidate histories state) (hs : Steps block candidate histories cluster plan state next) :
    Active block candidate histories next := by
  induction hs with
  | refl => exact hi
  | next first rest ih => exact ih (step_active hi first)

theorem available_pool_active {block candidate histories state}
    (hp : ∀ k owner, get? state.bytes k = some owner → owner = .available) : Active block candidate histories state := by
  intro loc node mode hh
  have he := hp (key loc) _ hh
  cases he

/-- The actual source/region public guard applies throughout the active-byte
protocol. Initial permissions are an available pool; initial runtime loans
come from real public preparation, not an assumed Borrowed certificate. -/
theorem active_byte_protects_host_region {tiles initial candidate} (family : Ptx.Kernels.HopperDoubleBuffer.ReplySourceFamily tiles candidate)
    (values : List Nat) (hv : values.length = 10) (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed Ptx.Kernels.HopperDoubleBuffer.code (Ptx.Kernels.HopperDoubleBuffer.completeLaunch tiles initial) candidate)
    (hc : Unified.Complete candidate) (hd : Tma.DescriptorAgreement candidate.view (Ptx.Kernels.HopperDoubleBuffer.dataMaps tiles))
    {pool histories state loc node mode target region}
    (hpool : ∀ k owner, get? pool k = some owner → owner = .available)
    (hs : Steps Ptx.Kernels.HopperStage.block candidate histories Ptx.Kernels.HopperDoubleBuffer.dataCluster
      (Ptx.Kernels.HopperDoubleBuffer.Whole.plan family)
      ⟨⟨Ptx.Kernels.HopperDoubleBuffer.Whole.prepared values tiles,fun _ => False⟩,pool⟩ state)
    (hheld : get? state.bytes (key loc) = some (.held node mode))
    (hl : Ptx.Kernels.HopperDoubleBuffer.Whole.layout tiles target = some region) (hcontains : region.Contains loc) :
    Ptx.Async.reclaim state.coupled.protocol target = .error .outstandingLoan ∧
      ∀ value, Ptx.Async.hostWrite state.coupled.protocol target value = .error .outstandingLoan := by
  have hi := steps_active (available_pool_active hpool) hs
  obtain ⟨⟨work,hu⟩,hr⟩ := hi loc node mode hheld
  exact Ptx.Kernels.HopperDoubleBuffer.Whole.public_pending_reclaim_write_rejected family values hv ht hb hw hc hd
    (steps_projects hs) hu hr.2.1 hl hcontains

end
end Ptx.Hopper.ByteAuthority
