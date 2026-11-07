import Ptx.Hopper.Memory
import Ptx.Tests.TmaConsumerObserver

/-! Independent witness for all current proxy-aware memory components of the
consumer helper. No observer output or universal correctness theorem is used
to establish the memory constraints. Broader ISA/runtime admission is separate. -/
namespace Ptx.TmaConsumerMemory
open Ptx.ISA Ptx.Hopper
open Ptx.TmaPublicationTests (candidate answer rf co histories cluster eid events trace)
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 500000

def rank : Access.Node → Nat
  | .tma node => TmaTests.rank node
  | .copyRead _ | .copyWrite _ => 0

def trueWaitTag : Hopper.Event → Bool
  | .barrier ⟨_,.tryWaitParity _ true⟩ => true
  | _ => false

theorem actual_wait_serial {n event where_ parity}
    (he : (candidate n).barrierAt event = some ⟨where_,.tryWaitParity parity true⟩) : event.serial = 4 := by
  obtain ⟨t,ht,_,hg⟩ := Ptx.Hopper.eventAt_trace (barrierAt_iff.mp he)
  have ht : t = trace n := List.mem_singleton.mp ht
  subst t
  have hb : event.serial < 8 := (List.getElem?_eq_some_iff.mp hg).1
  have hall : ∀ index : Fin 8, ((events n)[index.val]?).map trueWaitTag = some true → index.val = 4 := by
    intro index hh
    fin_cases index <;> simp [events,trueWaitTag] at hh ⊢
  change (events n)[event.serial]? = some (.barrier ⟨where_,.tryWaitParity parity true⟩) at hg
  apply hall ⟨event.serial,hb⟩
  change ((events n)[event.serial]?).map trueWaitTag = some true
  rw [hg]
  rfl

theorem generic_serial {n a b} (h : Access.GenericAfter (candidate n) a b) : a.serial < b.serial := by
  apply h.rank_lt (fun event => event.serial)
  intro x y he
  rcases he with hp | hc
  · exact hp.2.2.2
  · exact (TmaConsumerWitness.no_cta_sync n x y hc).elim

theorem write_location_shape {n id offset loc}
    (hl : Tma.writeLocation Tma.localShared (candidate n) id offset = some loc) :
    id = TmaTests.operation ∧ offset < 32 := by
  cases hc : Tma.copyAt (candidate n) id with
  | none => simp [Tma.writeLocation,hc] at hl
  | some op =>
    obtain ⟨rfl,rfl⟩ := TmaPublicationTests.only_copy hc
    simp only [Tma.writeLocation,hc,Option.bind_some] at hl
    split at hl
    · exact ⟨rfl,by assumption⟩
    · cases hl

theorem generic_rank {n a b} (h : Access.GenericEdge (candidate n) a b) :
    rank (.tma (.source a)) < rank (.tma (.source b)) := by
  rcases h with hp | hc
  · have hh := hp.2.2.2
    simp only [rank,TmaTests.rank]
    split_ifs <;> omega
  · exact (TmaConsumerWitness.no_cta_sync n a b hc).elim

theorem publication_rank {n a b loc} (h : Access.Published Tma.localShared (candidate n) histories cluster a b loc) : rank a < rank b := by
  unfold Access.Published at h
  split at h
  · obtain ⟨wait,hl,_,ho,ha⟩ := h
    obtain ⟨rfl,hbound⟩ := write_location_shape hl
    obtain ⟨_,_,parity,_,_,_,_,_,_,hw,_⟩ := Access.observed_has_actual_notification ho
    have hs := actual_wait_serial hw
    have hh := generic_serial ha
    simp only [rank,TmaTests.rank]
    split_ifs <;> omega
  · cases h

theorem protection_rank {n a b loc} (h : Access.Protected Tma.localShared (candidate n) a b loc) : rank a < rank b := by
  unfold Access.Protected at h
  split at h
  · obtain ⟨fence,hf,hbefore,_,hl,_⟩ := h
    obtain ⟨rfl,_⟩ := write_location_shape hl
    have hs := TmaConsumerWitness.actual_fence_serial hf
    have hh := hbefore.2.2.2
    simp only [rank,TmaTests.rank]
    split_ifs <;> omega
  · cases h

theorem byte_edge_rank {n loc a b} (he : Access.ByteEdge Tma.localShared Access.globalDescriptor (candidate n) histories cluster loc a b) : rank a < rank b := by
  rcases he with hg | hi | hc | ht | hp | hf
  · split at hg
    · exact generic_rank hg
    · cases hg
  · cases a <;> cases b <;> simp [Access.NonbulkInternal,TmaPublicationTests.no_nonbulk] at hi
  · cases a <;> cases b <;> simp [Access.NonbulkCompleted,TmaPublicationTests.no_nonbulk] at hc
    all_goals split at hc <;> cases hc
  · unfold Access.TensorInternal at ht
    split at ht
    · rcases ht with ⟨rfl,rfl,_⟩
      simp only [rank,TmaTests.rank]
      omega
    · cases ht
  · exact publication_rank hp
  · exact protection_rank hf

theorem byte_order_rank {n loc a b}
    (ho : Access.ByteOrder Tma.localShared Access.globalDescriptor (candidate n) histories cluster loc a b) : rank a < rank b :=
  ho.rank_lt rank (fun _ _ he => byte_edge_rank he)

theorem causal_rank {loc a b}
    (hc : Access.CausalityAt Tma.localShared Access.globalDescriptor (candidate answer) histories cluster rf loc a b) : rank a < rank b := by
  rcases hc with ⟨_,_,ho⟩ | ⟨_,hobs,_⟩
  · exact byte_order_rank ho
  · exact (TmaConsumerWitness.no_observation _ _ hobs).elim

theorem unique_writer {n loc a b va vb}
    (ha : Access.writeByte Tma.localShared Access.globalDescriptor (candidate n) a loc = some va)
    (hb : Access.writeByte Tma.localShared Access.globalDescriptor (candidate n) b loc = some vb) : a = b := by
  rcases TmaEligibilityTests.write_inventory ha with ⟨hida,hsa,_⟩ | ⟨hida,hsa,_⟩
  · rcases TmaEligibilityTests.write_inventory hb with ⟨hidb,_,_⟩ | ⟨_,hsb,_⟩
    · exact hida.trans hidb.symm
    · simp [hsa] at hsb
  · rcases TmaEligibilityTests.write_inventory hb with ⟨_,hsb,_⟩ | ⟨hidb,_,_⟩
    · simp [hsa] at hsb
    · exact hida.trans hidb.symm

theorem coherence_witness : Access.Coherent Tma.localShared Access.globalDescriptor (candidate answer) histories cluster rf co := by
  apply Access.unique_initial_coherent (fun _ _ _ _ _ ha hb => unique_writer ha hb)
  intro loc writer value hw hc
  exact Nat.lt_irrefl _ (causal_rank hc)

theorem no_strong_read_write {n read writer loc vr vw}
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (candidate n) read loc = some vr)
    (hw : Access.writeByte Tma.localShared Access.globalDescriptor (candidate n) writer loc = some vw) :
    ¬ Access.MorallyStrong Tma.localShared Access.globalDescriptor (candidate n) read writer := by
  intro hs
  rcases TmaEligibilityTests.write_inventory hw with ⟨_,hg,hlo,_⟩ | ⟨hid,hg,_⟩
  · exact TmaConsumerWitness.output_write_cannot_overlap_read hr hg hlo
  · obtain ⟨rfl,_,_,_⟩ := TmaConsumerWitness.shared_read_site hr hg
    subst writer
    have hp := hs.1
    cases hp

theorem no_rmw (n : Nat) (node : Access.Node) : ¬ (Access.inventoryGraph Tma.localShared Access.globalDescriptor (candidate n)).IsRMW node := by
  rintro ⟨scope,base,payload,hk⟩
  change Access.kind Tma.localShared Access.globalDescriptor (candidate n) node = some (.rmw scope base payload) at hk
  cases node with
  | copyRead issue | copyWrite issue => simp [Access.kind,TmaPublicationTests.no_nonbulk] at hk
  | tma node =>
    cases node with
    | source event =>
      rcases TmaEligibilityTests.source_memory_id hk with ⟨_,he⟩ | ⟨_,he⟩ <;> cases he
    | descriptor id => cases hc : Tma.copyAt (candidate n) id <;> simp [Access.kind,hc] at hk
    | read id offset => obtain ⟨_,_,_,_,he⟩ := Access.tensor_read_shape hk; cases he
    | write id offset => obtain ⟨_,_,_,_,he⟩ := Access.tensor_write_shape hk; cases he
    | notify id => cases hk

theorem communication_not_strong {a b}
    (hs : Access.MorallyStrong Tma.localShared Access.globalDescriptor (candidate answer) a b) :
    ¬ Access.Communication Tma.localShared Access.globalDescriptor (candidate answer) rf co a b := by
  rintro (⟨loc,value,hr,_,hw⟩ | ⟨_,hc⟩ | ⟨_,loc,value,hr,hc⟩)
  · obtain ⟨vw,hwrite⟩ := Option.isSome_iff_exists.mp hw
    exact no_strong_read_write hr hwrite (Access.strong_symm hs)
  · cases hc.1
  · obtain ⟨writer,he,hw⟩ := hc.2
    have hid : b = writer := Option.some.inj he
    subst writer
    obtain ⟨vw,hwrite⟩ := Option.isSome_iff_exists.mp hw
    exact no_strong_read_write hr hwrite hs

theorem program_rank {n a b} (hp : Access.ProgramOrder (candidate n) a b) : rank a < rank b := by
  unfold Access.ProgramOrder at hp
  split at hp
  · unfold Tma.ProgramOrder at hp
    split at hp
    · exact generic_rank (.inl hp)
    · cases hp
  · cases hp

theorem sc_per_location : Access.SCPerLocation Tma.localShared Access.globalDescriptor (candidate answer) rf co := by
  intro members _ hm a _ hp
  have hh := hp.rank_lt rank (by
    rintro x y ⟨hx,hy,he⟩
    rcases he with hpo | hc
    · exact program_rank hpo
    · exact (communication_not_strong (hm x y hx hy).1 hc).elim)
  omega

theorem memory_witness : Access.MemoryConditions Tma.localShared Access.globalDescriptor (candidate answer) TmaInputTests.initial rf co histories cluster := by
  refine ⟨TmaConsumerWitness.causal_witness,?_,fun _ => coherence_witness,?_,?_,fun _ => sc_per_location⟩
  · intro loc node ho
    exact Nat.lt_irrefl _ (byte_order_rank ho)
  · intro _ read writer hs loc vr vw hr hw
    exact (no_strong_read_write hr hw hs).elim
  · intro _ atomic writer hrmw
    exact (no_rmw answer atomic hrmw).elim

theorem memory_and_observer :
    Access.MemoryConditions Tma.localShared Access.globalDescriptor (candidate answer) TmaInputTests.initial rf co histories cluster ∧
    Access.ObserverConditions Tma.localShared Access.globalDescriptor (candidate answer) TmaInputTests.initial rf co histories cluster TmaConsumerObserver.observation :=
  ⟨memory_witness,TmaConsumerObserver.observer_witness⟩

end
end Ptx.TmaConsumerMemory
