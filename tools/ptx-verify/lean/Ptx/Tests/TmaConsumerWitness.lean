import Ptx.Tests.TmaEligibility
import Ptx.Tests.TmaInputCausal

/-! An independent causal witness for every real descriptor, TMA input and
generic consumer read in the actual publication helper. Output/observer and
full coherence/atomicity/ISA admission are separate from these causal facts. -/
namespace Ptx.TmaConsumerWitness
open Ptx.ISA Ptx.Hopper
open Ptx.TmaPublicationTests (candidate answer rf co histories cluster eid events trace bytes)
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 500000

theorem copy_view_eq (n : Nat) (actual : Tma.CopyId) : Tma.copyAt (candidate n) actual = Tma.copyAt TmaTests.candidate actual := by
  cases hn : Tma.copyAt (candidate n) actual with
  | some op => obtain ⟨rfl,rfl⟩ := TmaPublicationTests.only_copy hn; rfl
  | none =>
    cases ho : Tma.copyAt TmaTests.candidate actual with
    | none => rfl
    | some op =>
      obtain ⟨rfl,rfl⟩ := TmaInputTests.only_copy ho
      have hx : Tma.copyAt (candidate n) TmaTests.operation = some TmaTests.copy := by rfl
      rw [hx] at hn
      cases hn

theorem lifted_read_agrees {node loc value}
    (hk : Access.kind Tma.localShared Access.globalDescriptor (candidate answer) node =
      Access.kind Tma.localShared Access.globalDescriptor TmaTests.candidate node)
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (candidate answer) node loc = some value) :
    Access.sourceValue Tma.localShared Access.globalDescriptor (candidate answer) TmaInputTests.initial node loc (rf node loc) = some value := by
  have ho : Access.readByte Tma.localShared Access.globalDescriptor TmaTests.candidate node loc = some value := by
    simpa only [Access.readByte,hk] using hr
  have hglobal := TmaInputCausalTests.every_read_global ho
  have hv := TmaInputCausalTests.every_read_agrees ho
  simpa [Access.sourceValue,rf,hglobal,TmaInputTests.rf] using hv

theorem every_read_agrees {node loc value}
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (candidate answer) node loc = some value) :
    Access.sourceValue Tma.localShared Access.globalDescriptor (candidate answer) TmaInputTests.initial node loc (rf node loc) = some value := by
  cases node with
  | copyRead issue | copyWrite issue => simp [Access.readByte,Access.kind,TmaPublicationTests.no_nonbulk] at hr
  | tma node =>
    cases node with
    | source event =>
      obtain ⟨k,hk⟩ := Access.access_kind (show Access.Accesses Tma.localShared Access.globalDescriptor (candidate answer) _ loc from .inl (by rw [hr]; rfl))
      rcases TmaEligibilityTests.source_memory_id hk with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · have hb := Access.access_bounds (show Access.Accesses Tma.localShared Access.globalDescriptor (candidate answer) _ loc from .inl (by rw [hr]; rfl))
          (show (Access.kind Tma.localShared Access.globalDescriptor (candidate answer) _).bind Ptx.Event.Kind.footprint = some (⟨.shared .zero,16⟩,4) by simp [hk,Ptx.Event.Kind.footprint,bytes])
        exact TmaPublicationTests.witness_agreement _ loc value ⟨rfl,hb.1.symm,hb.2⟩ hr
      · simp [Access.readByte,hk,Ptx.Event.Kind.readByte] at hr
    | descriptor actual =>
      apply lifted_read_agrees ?_ hr
      simp only [Access.kind,copy_view_eq]
    | read actual offset =>
      apply lifted_read_agrees ?_ hr
      simp only [Access.kind,Tma.readLocation,Tma.transferByte,copy_view_eq]
    | write actual offset =>
      apply lifted_read_agrees ?_ hr
      simp only [Access.kind,Tma.writeLocation,Tma.transferByte,copy_view_eq]
    | notify actual => cases hr

def fenceTag : Hopper.Event → Bool
  | .proxyFenceAsyncShared _ => true
  | _ => false

theorem actual_fence_serial {n event cta} (he : (candidate n).eventAt event = some (.proxyFenceAsyncShared cta)) : event.serial = 1 := by
  obtain ⟨t,ht,_,hg⟩ := Ptx.Hopper.eventAt_trace he
  have ht : t = trace n := List.mem_singleton.mp ht
  subst t
  have hb : event.serial < 8 := (List.getElem?_eq_some_iff.mp hg).1
  have hall : ∀ index : Fin 8, ((events n)[index.val]?).map fenceTag = some true → index.val = 1 := by
    intro index hh
    fin_cases index <;> simp [events,fenceTag] at hh ⊢
  change (events n)[event.serial]? = some (.proxyFenceAsyncShared cta) at hg
  apply hall ⟨event.serial,hb⟩
  change ((events n)[event.serial]?).map fenceTag = some true
  rw [hg]
  rfl

theorem no_cta_sync (n : Nat) : ∀ a b, ¬ Hopper.CTAControl (candidate n) a b := by
  have tag_none : ∀ event arrival, (candidate n).ctaTag arrival event = none := by
    intro event arrival
    cases he : (candidate n).eventAt event with
    | none => simp [Candidate.ctaTag,he]
    | some e =>
      have hm := TmaPublicationTests.event_member he
      simp only [events,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        cases arrival <;> simp [Candidate.ctaTag,he]
  intro a b hc
  simp only [Hopper.CTAControl,tag_none] at hc

theorem source_suffix_closed {n loc a b}
    (ho : Access.ByteOrder Tma.localShared Access.globalDescriptor (candidate n) histories cluster loc a b)
    (hs : ∃ event, a = .tma (.source event) ∧ 5 ≤ event.serial) :
    ∃ event, b = .tma (.source event) ∧ 5 ≤ event.serial := by
  apply Access.source_region_order (fun event => 5 ≤ event.serial) ?_ ?_ ho hs
  · intro x y hx he
    rcases he with hp | hc
    · have hh := hp.2.2.2; omega
    · exact (no_cta_sync n x y hc).elim
  · intro x target hx hp
    cases target with
    | copyRead _ | copyWrite _ => cases hp
    | tma node =>
      cases node with
      | write actual offset =>
        obtain ⟨fence,hf,hbefore,_⟩ := hp
        have hserial := actual_fence_serial hf
        have hh := hbefore.2.2.2
        omega
      | source _ | descriptor _ | read _ _ | notify _ => cases hp

theorem shared_read_site {n node loc value}
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (candidate n) node loc = some value)
    (hs : loc.space = .shared .zero) : TmaPublicationTests.ConsumerSite node loc := by
  rcases TmaEligibilityTests.shared_access_inventory (.inl (by rw [hr]; rfl)) hs with ⟨rfl,hlo,hhi⟩ | hid
  · exact ⟨rfl,hs,hlo,hhi⟩
  · subst node
    obtain ⟨k,hk⟩ := Access.access_kind (show Access.Accesses Tma.localShared Access.globalDescriptor (candidate n) _ loc from .inl (by rw [hr]; rfl))
    obtain ⟨where_,byte,_,_,rfl⟩ := Access.tensor_write_shape hk
    simp [Access.readByte,hk,Ptx.Event.Kind.readByte] at hr

theorem no_observation : ∀ a b, ¬ Access.ObservationOrder Tma.localShared Access.globalDescriptor (candidate answer) rf a b := by
  apply Access.observation_order_absent
  rintro writer read ⟨hstrong,loc,value,hr,hs,_⟩
  have hshape : loc.space = .shared .zero ∧ 16 ≤ loc.address ∧ loc.address < 20 := by
    unfold rf at hs
    split at hs
    · assumption
    · cases hs
  have hid : writer = .tma (.write TmaTests.operation (loc.address-16)) := by simpa [rf,hshape] using hs.symm
  obtain ⟨rfl,_,_,_⟩ := shared_read_site hr hshape.1
  subst writer
  have hp := hstrong.1
  cases hp

theorem output_write_cannot_overlap_read {n loc value writer}
    (hr : Access.readByte Tma.localShared Access.globalDescriptor (candidate n) writer loc = some value)
    (hs : loc.space = .global) (hlo : 8192 ≤ loc.address) : False := by
  have hid := TmaEligibilityTests.output_access_inventory (.inl (by rw [hr]; rfl)) hs hlo
  subst writer
  change none = some value at hr
  cases hr

theorem causal_witness : Access.CausalConstraints Tma.localShared Access.globalDescriptor (candidate answer) TmaInputTests.initial rf co histories cluster := by
  refine ⟨fun _ _ _ _ hr => every_read_agrees hr,?_,?_,?_⟩
  · intro _ writer loc value hw
    exact ⟨rfl,writer,rfl,by rw [hw]; rfl⟩
  · intro _ writer read loc vw vr hw hr _ hco
    rcases TmaEligibilityTests.write_inventory hw with ⟨_,hs,hlo,_⟩ | ⟨hid,hs,hlo,hhi⟩
    · exact (output_write_cannot_overlap_read hr hs hlo).elim
    · have hsite := shared_read_site hr hs
      have hrf : (rf read loc).isSome = true := by simp [rf,hsite.2.1,hsite.2.2]
      have he := hco.1
      rw [he] at hrf
      cases hrf
  · intro _ read writer loc vr vw hr hw hc _
    rcases TmaEligibilityTests.write_inventory hw with ⟨_,hs,hlo,_⟩ | ⟨hid,hs,_,_⟩
    · exact (output_write_cannot_overlap_read hr hs hlo).elim
    · obtain ⟨rfl,_,_,_⟩ := shared_read_site hr hs
      subst writer
      rcases hc with ⟨_,_,ho⟩ | ⟨_,hobs,_⟩
      · obtain ⟨event,he,_⟩ := source_suffix_closed ho ⟨eid 5,rfl,by decide⟩
        cases he
      · exact no_observation _ _ hobs

end
end Ptx.TmaConsumerWitness
