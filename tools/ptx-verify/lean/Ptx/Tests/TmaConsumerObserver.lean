import Ptx.Hopper.Observation
import Ptx.Tests.TmaConsumerWitness

/-! Independent complete global observation and universal observed byte/frame
contracts for the actual one-thread publication family, relative to the causal
and observer components. Full ISA/proxy/coherence/atomicity admission is still
distinct; this helper does not close the required Hopper GEMM case. -/
namespace Ptx.TmaConsumerObserver
open Ptx.ISA Ptx.Hopper
open Ptx.TmaPublicationTests (candidate answer rf co histories cluster eid)
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 500000

def domain : List Location := (List.range 16).map (fun offset => ⟨.global,8188+offset⟩)
def select (loc : Location) : Option Access.Node :=
  if loc.space = .global ∧ 8192 ≤ loc.address ∧ loc.address < 8196 then some (.tma (.source (eid 6))) else none
def observation : Access.Observation := Access.selectedObservation Tma.localShared Access.globalDescriptor (candidate answer)
  TmaInputTests.initial select domain

theorem mem_domain {loc} : loc ∈ domain ↔ loc.space = .global ∧ 8188 ≤ loc.address ∧ loc.address < 8204 := by
  constructor
  · intro hm
    obtain ⟨offset,ho,rfl⟩ := List.mem_map.mp hm
    have hb := List.mem_range.mp ho
    exact ⟨rfl,by change 8188 ≤ 8188+offset; omega,by change 8188+offset < 8204; omega⟩
  · rintro ⟨hs,hlo,hhi⟩
    refine List.mem_map.mpr ⟨loc.address-8188,List.mem_range.mpr (by omega),?_⟩
    rcases loc with ⟨space,address⟩
    simp only at hs hlo hhi
    simp only [Location.mk.injEq]
    exact ⟨hs.symm,by omega⟩

theorem global_writer {n loc writer value}
    (hs : loc.space = .global)
    (hw : Access.writeByte Tma.localShared Access.globalDescriptor (candidate n) writer loc = some value) :
    writer = .tma (.source (eid 6)) ∧ 8192 ≤ loc.address ∧ loc.address < 8196 := by
  rcases TmaEligibilityTests.write_inventory hw with ⟨hid,_,hb⟩ | ⟨_,hshared,_⟩
  · exact ⟨hid,hb⟩
  · simp [hs] at hshared

theorem coherence_irrefl (loc source) : ¬ co loc source source := by
  rintro ⟨hleft,writer,hright,_⟩
  have he : (none : Option Access.Node) = some writer := hleft.symm.trans hright
  cases he

theorem observer_witness : Access.ObserverConditions Tma.localShared Access.globalDescriptor (candidate answer) TmaInputTests.initial
    rf co histories cluster observation := by
  apply Access.selected_observer (TmaPublicationTests.complete answer)
  · intro loc hl; exact (mem_domain.mp hl).1
  · intro writer loc value hs hw
    have hb := global_writer hs hw
    exact mem_domain.mpr ⟨hs,by omega,by omega⟩
  · intro loc hl writer value hw
    obtain ⟨hid,hlo,hhi⟩ := global_writer (mem_domain.mp hl).1 hw
    simp [select,(mem_domain.mp hl).1,hlo,hhi,hid]
  · exact coherence_irrefl

theorem observer_eligible (n : Nat) (rfs : Access.ReadsFrom) (loc : Location) :
    Access.ObserverEligible Tma.localShared Access.globalDescriptor (candidate n) histories cluster rfs loc :=
  Access.race_free_observer_eligible (TmaEligibilityTests.race_free n rfs) loc

theorem observed_output {n initial rfs cos obs}
    (hc : Access.CausalConstraints Tma.localShared Access.globalDescriptor (candidate n) initial rfs cos histories cluster)
    (ho : Access.ObserverConditions Tma.localShared Access.globalDescriptor (candidate n) initial rfs cos histories cluster obs)
    (offset : Fin 4) : obs.output ⟨.global,8192+offset.val⟩ = .bits (byte (196+offset.val)) := by
  have hv := Access.causality_visibility hc (TmaEligibilityTests.eligible n rfs (.tma (.source (eid 5))) ⟨.shared .zero,16⟩).1
  have hk := TmaPublicationTests.actual_store_value hv (fun _ => TmaEligibilityTests.eligible n rfs _ _)
  have hw : Access.writeByte Tma.localShared Access.globalDescriptor (candidate n) (.tma (.source (eid 6)))
      ⟨.global,8192+offset.val⟩ = some (.bits (byte (196+offset.val))) := by
    simp only [Access.writeByte,hk,Option.bind_some,Ptx.Event.Kind.writeByte]
    fin_cases offset <;> rfl
  have hd := ho.coverage _ _ _ rfl hw
  apply Access.observer_unique_writer hc ho hd (observer_eligible n rfs _) hw
  intro other value hother
  exact (global_writer rfl hother).1

theorem observed_frame {n initial rfs cos obs loc}
    (ho : Access.ObserverConditions Tma.localShared Access.globalDescriptor (candidate n) initial rfs cos histories cluster obs)
    (hd : loc ∈ obs.domain) (hs : loc.space = .global)
    (hf : ¬ (8192 ≤ loc.address ∧ loc.address < 8196)) : obs.output loc = initial .generic loc := by
  apply Access.observer_unwritten ho hd (observer_eligible n rfs loc)
  intro writer
  cases hw : Access.writeByte Tma.localShared Access.globalDescriptor (candidate n) writer loc with
  | none => rfl
  | some value => exact (hf (global_writer hs hw).2).elim

theorem independent_complete_witness :
    WellFormed Generated.hopper_tma_publish.program TmaPublicationTests.launch (candidate answer) ∧
    Complete (candidate answer) ∧
    Access.CausalConstraints Tma.localShared Access.globalDescriptor (candidate answer) TmaInputTests.initial rf co histories cluster ∧
    Access.ObserverConditions Tma.localShared Access.globalDescriptor (candidate answer) TmaInputTests.initial rf co histories cluster observation :=
  ⟨TmaPublicationTests.formed answer,TmaPublicationTests.complete answer,TmaConsumerWitness.causal_witness,observer_witness⟩

theorem concrete_observed_word : ∀ offset : Fin 4, observation.output ⟨.global,8192+offset.val⟩ = .bits (byte (196+offset.val)) :=
  observed_output TmaConsumerWitness.causal_witness observer_witness

theorem concrete_padding_preserved : observation.output ⟨.global,8196⟩ = TmaTests.initial ⟨.global,8196⟩ :=
  observed_frame observer_witness (by apply mem_domain.mpr; decide) rfl (by decide)

def incomplete : Access.Observation := {observation with domain := []}
theorem omitted_global_write_rejected : ¬ Access.ObserverConditions Tma.localShared Access.globalDescriptor (candidate answer)
    TmaInputTests.initial rf co histories cluster incomplete := by
  intro ho
  have hw : Access.writeByte Tma.localShared Access.globalDescriptor (candidate answer) (.tma (.source (eid 6)))
      ⟨.global,8192⟩ = some (.bits (byte 196)) := by rfl
  have hh := ho.coverage _ _ _ rfl hw
  cases hh

def stale : Access.Observation := {observation with source := fun _ => none,output := TmaInputTests.initial .generic}
theorem stale_initialization_rejected : ¬ Access.ObserverConditions Tma.localShared Access.globalDescriptor (candidate answer)
    TmaInputTests.initial rf co histories cluster stale := by
  intro ho
  have hw : Access.writeByte Tma.localShared Access.globalDescriptor (candidate answer) (.tma (.source (eid 6)))
      ⟨.global,8192⟩ = some (.bits (byte 196)) := by rfl
  have hh := ho.noStale _ (by apply mem_domain.mpr; decide)
    (TmaEligibilityTests.eligible answer rf (.tma (.source (eid 5))) ⟨.shared .zero,16⟩).1 _ _ hw
  exact hh ⟨rfl,_,rfl,by rw [hw]; rfl⟩

end
end Ptx.TmaConsumerObserver
