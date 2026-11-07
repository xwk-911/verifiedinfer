import Ptx.Tests.TmaConsumerMemory

/-! Join actual source/resource/control, proxy-aware memory and global observer
evidence for the publication helper. This is relative to the current abstract
components, with descriptor encoding/runtime and complete ISA/lifetime checks
remaining outside the claim. The required Hopper GEMM case remains separate. -/
namespace Ptx.TmaConsumerChecked
open Ptx.ISA Ptx.Hopper
open Ptx.TmaPublicationTests (candidate answer rf co histories cluster eid history)
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 500000

theorem all_resource_locations (n : Nat) : ∀ origin ∈ Tma.origins (candidate n), ∀ data,
    Tma.resourceAt Tma.localShared (candidate n) origin = some data → data.location = TmaTests.loc := by
  have ho : Tma.origins (candidate n) = [.source (eid 0),.source (eid 2),.source (eid 4),.source (eid 7),.notification TmaTests.operation] := by rfl
  intro origin hm data he
  rw [ho] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  have hl : (Tma.resourceAt Tma.localShared (candidate n) origin).map BarrierEvent.location = some TmaTests.loc := by
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [he] at hl
  exact Option.some.inj hl

theorem all_histories (n : Nat) : ∀ loc, Tma.HistoryValid Tma.localShared (candidate n) loc (histories loc) := by
  intro loc
  by_cases he : loc = TmaTests.loc
  · subst loc; simpa [histories] using TmaPublicationTests.history_valid n
  · have hi : Tma.inventory Tma.localShared (candidate n) loc = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro entry hm
      have hh := Tma.inventory_iff.mp hm
      exact he (all_resource_locations n entry.origin (Tma.origin_mem hh) _ hh)
    refine ⟨by simp [histories,he],?_,?_,?_⟩
    · simp [histories,he,hi]
    · simp [histories,he,Tma.SourceOrder]
    · exact ⟨none,by simp [histories,he,Mbarrier.run]⟩

theorem source_rank {n a b} (hp : Tma.ProgramOrder (candidate n) a b) :
    TmaConsumerMemory.rank (.tma a) < TmaConsumerMemory.rank (.tma b) := by
  unfold Tma.ProgramOrder at hp
  split at hp
  · exact TmaConsumerMemory.generic_rank (.inl hp)
  · cases hp

theorem cta_rank {n a b} (hc : Tma.CTAControl (candidate n) a b) :
    TmaConsumerMemory.rank (.tma a) < TmaConsumerMemory.rank (.tma b) := by
  unfold Tma.CTAControl at hc
  split at hc
  · exact (TmaConsumerWitness.no_cta_sync n _ _ hc).elim
  · cases hc

theorem internal_rank {n a b} (he : Tma.InternalEdge (candidate n) a b) :
    TmaConsumerMemory.rank (.tma a) < TmaConsumerMemory.rank (.tma b) := by
  cases he with
  | issue hc =>
    obtain ⟨op,hh⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨rfl,_⟩ := TmaPublicationTests.only_copy hh
    decide
  | descriptorRead _ | descriptorWrite _ | data _ => simp only [TmaConsumerMemory.rank,TmaTests.rank]; omega
  | complete hw =>
    obtain ⟨op,hc,ho⟩ := Tma.write_has_copy hw
    obtain ⟨rfl,rfl⟩ := TmaPublicationTests.only_copy hc
    change _ < 32 at ho
    simp only [TmaConsumerMemory.rank,TmaTests.rank]
    omega

theorem resource_rank {a b} (he : Tma.ResourceEdge histories a b) :
    TmaConsumerMemory.rank (.tma a) < TmaConsumerMemory.rank (.tma b) := by
  have hr : ∀ left ∈ history, ∀ right ∈ history, Tma.Before history left.origin right.origin →
      TmaConsumerMemory.rank (.tma left.origin.node) < TmaConsumerMemory.rank (.tma right.origin.node) := by decide
  obtain ⟨loc,left,hl,right,hrr,hb,rfl,rfl⟩ := he
  by_cases he : loc = TmaTests.loc
  · subst loc
    exact hr left (by simpa [histories] using hl) right (by simpa [histories] using hrr) (by simpa [histories] using hb)
  · simp [histories,he] at hl

theorem control_acyclic (n : Nat) : Tma.ControlAcyclic (candidate n) histories :=
  Tma.control_acyclic_of_rank (fun node => TmaConsumerMemory.rank (.tma node))
    (fun _ _ he => source_rank he) (fun _ _ he => cta_rank he) (fun _ _ he => internal_rank he) (fun _ _ he => resource_rank he)

theorem source_components (n : Nat) : Tma.Components Generated.hopper_tma_publish.program TmaPublicationTests.launch (candidate n)
    Tma.localShared TmaTests.maps histories := by
  refine ⟨TmaPublicationTests.formed n,TmaPublicationTests.complete n,?_,?_,all_histories n,control_acyclic n⟩
  · intro actual op hc
    obtain ⟨rfl,rfl⟩ := TmaPublicationTests.only_copy hc
    rfl
  · intro actual op hc offset ho
    obtain ⟨rfl,rfl⟩ := TmaPublicationTests.only_copy hc
    exact TmaTests.payload_byte ⟨offset,ho⟩

theorem generic_initial_matches_launch : TmaInputTests.initial .generic = TmaPublicationTests.launch.initial := by rfl

theorem async_initial_matches_launch : TmaInputTests.initial .async = TmaPublicationTests.launch.initial := by rfl

theorem complete_component_witness :
    TmaInputTests.initial .generic = TmaPublicationTests.launch.initial ∧
    TmaInputTests.initial .async = TmaPublicationTests.launch.initial ∧
    Tma.Components Generated.hopper_tma_publish.program TmaPublicationTests.launch (candidate answer) Tma.localShared TmaTests.maps histories ∧
    Access.MemoryConditions Tma.localShared Access.globalDescriptor (candidate answer) TmaInputTests.initial rf co histories cluster ∧
    Access.ObserverConditions Tma.localShared Access.globalDescriptor (candidate answer) TmaInputTests.initial rf co histories cluster TmaConsumerObserver.observation :=
  ⟨generic_initial_matches_launch,async_initial_matches_launch,source_components answer,TmaConsumerMemory.memory_witness,TmaConsumerObserver.observer_witness⟩

theorem bad_reply_passes_control_but_fails_memory :
    Tma.Components Generated.hopper_tma_publish.program TmaPublicationTests.launch (candidate 0) Tma.localShared TmaTests.maps histories ∧
    ∀ initial rfs cos, ¬ Access.MemoryConditions Tma.localShared Access.globalDescriptor (candidate 0) initial rfs cos histories cluster := by
  refine ⟨source_components 0,?_⟩
  intro initial rfs cos hm
  exact TmaEligibilityTests.zero_reply_inadmissible hm.toCausalConstraints

end
end Ptx.TmaConsumerChecked
