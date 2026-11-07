import Ptx.Tests.TmaPhases
import Ptx.Hopper.ByteOrder

/-! Actual local source prefixes isolate the memory effect of the shared proxy
fence. They are not complete ISA-valid kernel executions: resource lifecycle,
allocation, completion and other launch obligations remain separate. -/
namespace Ptx.TmaRaceTests
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 500000

def candidate := TmaPhaseTests.noFenceCandidate
def read : Access.Node := .tma (.source (TmaPhaseTests.eid 0))
def writer : Access.Node := .tma (.write ⟨TmaPhaseTests.eid 1⟩ 0)
def loc : Location := ⟨.shared .zero,16⟩

theorem no_fence (event cta) : candidate.eventAt event ≠ some (.proxyFenceAsyncShared cta) := by
  intro he
  obtain ⟨t,ht,_,hg⟩ := Ptx.Hopper.eventAt_trace he
  have ht : t = TmaPhaseTests.noFenceTrace := List.mem_singleton.mp ht
  subst t
  have hm := List.mem_of_getElem? hg
  simp [TmaPhaseTests.noFenceTrace,TmaPhaseTests.reuseEvents] at hm

theorem no_wait (event where_ parity) : candidate.barrierAt event ≠ some ⟨where_,.tryWaitParity parity true⟩ := by
  intro he
  obtain ⟨t,ht,_,hg⟩ := Ptx.Hopper.eventAt_trace (barrierAt_iff.mp he)
  have ht : t = TmaPhaseTests.noFenceTrace := List.mem_singleton.mp ht
  subst t
  have hm := List.mem_of_getElem? hg
  simp [TmaPhaseTests.noFenceTrace,TmaPhaseTests.reuseEvents] at hm

theorem no_publication {histories cluster target where_} : ¬ Access.Published Tma.localShared candidate histories cluster writer target where_ := by
  intro hp
  cases target with
  | copyRead _ | copyWrite _ => cases hp
  | tma node =>
    cases node with
    | source event =>
      obtain ⟨wait,hc,_⟩ := Access.published_requires_observed_completion hp
      obtain ⟨where_,_,parity,_,_,_,_,_,_,he,_⟩ := Access.observed_has_actual_notification hc
      exact no_wait wait where_ parity he
    | descriptor _ | read _ _ | write _ _ | notify _ => cases hp

theorem unordered_read_writer {histories cluster} :
    ¬ Access.CausalityAt Tma.localShared Access.globalDescriptor candidate histories cluster (fun _ _ => none) loc read writer := by
  rintro (⟨_,_,ho⟩ | ⟨_,hobs,_⟩)
  · obtain ⟨event,he⟩ := Access.no_fence_order_from_source no_fence ho ⟨TmaPhaseTests.eid 0,rfl⟩
    cases he
  · exact Access.initial_rf_no_observation hobs

theorem unordered_writer_read {histories cluster} :
    ¬ Access.CausalityAt Tma.localShared Access.globalDescriptor candidate histories cluster (fun _ _ => none) loc writer read := by
  rintro (⟨_,_,ho⟩ | ⟨_,hobs,_⟩)
  · obtain ⟨target,hp⟩ := Access.tensor_write_first_publication ho ⟨TmaPhaseTests.eid 1⟩ 0 rfl
    exact no_publication hp
  · exact Access.initial_rf_no_observation hobs

theorem missing_fence_mixed_race (histories cluster) :
    Access.MixedSizeRace Tma.localShared Access.globalDescriptor candidate histories cluster (fun _ _ => none) := by
  refine ⟨loc,read,writer,?_,?_⟩
  · exact ⟨.inl (by rfl),.inr (by rfl),.inr (by rfl),unordered_read_writer,unordered_writer_read,
      fun he => by have hp := he.1; cases hp⟩
  · rintro ⟨footprint,hr,hw⟩
    have hread : (Access.kind Tma.localShared Access.globalDescriptor candidate read).bind Ptx.Event.Kind.footprint = some (loc,4) := by rfl
    have hwrite : (Access.kind Tma.localShared Access.globalDescriptor candidate writer).bind Ptx.Event.Kind.footprint = some (loc,1) := by rfl
    have he := congrArg Prod.snd (Option.some.inj ((hread.symm.trans hr).trans (hw.symm.trans hwrite)))
    cases he

theorem mixed_race_disables_all_reads (histories cluster node where_) :
    ¬ Access.Eligible Tma.localShared Access.globalDescriptor candidate histories cluster (fun _ _ => none) node where_ :=
  Access.mixed_size_disables_eligibility (missing_fence_mixed_race histories cluster) node where_

theorem fence_orders_the_conflict (histories cluster rf) :
    ¬ Access.DataRaceAt Tma.localShared Access.globalDescriptor TmaPhaseTests.reuseCandidate histories cluster rf loc
      (.tma (.source (TmaPhaseTests.eid 0))) (.tma (.write TmaPhaseTests.nextCopy 0)) := by
  intro hr
  exact hr.notForward (Access.byte_order_causal (.inl (by rfl)) (.inr (by rfl))
    (Access.protected_byte_order TmaPhaseTests.fence_protects_future_byte))

end
end Ptx.TmaRaceTests
