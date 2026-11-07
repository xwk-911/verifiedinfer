import Ptx.Hopper.ByteVisibility

/-! Completed generic-proxy observation over the combined Hopper inventory.
The domain must cover every actual global write; initialization cannot hide
an unobserved emitted write. Eligibility uses the byte/proxy-aware race model.
This does not prove CUDA API/physical observer correspondence or full ISA
admission. Initial observation values use the explicit generic proxy view. -/
namespace Ptx.Hopper.Access
open Ptx.ISA
noncomputable section

structure Observation where
  domain : List Location
  output : Location → Symbolic.Byte
  source : Location → Option Node

def observerValue (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (initial : ProxyMemory) (loc : Location) : Option Node → Option Symbolic.Byte
  | none => some (initial .generic loc)
  | some writer => writeByte resolve descriptor c writer loc

def ObserverEligible (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (rf : ReadsFrom) (loc : Location) : Prop :=
  ¬ MixedSizeRace resolve descriptor c histories cluster rf ∧
  ¬ ∃ a b, WritesAt resolve descriptor c a loc ∧ WritesAt resolve descriptor c b loc ∧
    DataRaceAt resolve descriptor c histories cluster rf loc a b

structure ObserverConditions (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (initial : ProxyMemory) (rf : ReadsFrom) (co : Location → Option Node → Option Node → Prop)
    (histories : Location → List Tma.Entry) (cluster : ClusterScope) (o : Observation) : Prop where
  complete : Complete c
  globalOnly : ∀ loc ∈ o.domain, loc.space = .global
  coverage : ∀ writer loc value, loc.space = .global → writeByte resolve descriptor c writer loc = some value → loc ∈ o.domain
  agreement : ∀ loc ∈ o.domain, ObserverEligible resolve descriptor c histories cluster rf loc →
    observerValue resolve descriptor c initial loc (o.source loc) = some (o.output loc)
  noStale : ∀ loc ∈ o.domain, ¬ MixedSizeRace resolve descriptor c histories cluster rf →
    ∀ writer value, writeByte resolve descriptor c writer loc = some value → ¬ co loc (o.source loc) (some writer)

def selectedObservation (resolve : Tma.SharedResolver) (descriptor : DescriptorResolver) (c : Candidate)
    (initial : ProxyMemory) (select : Location → Option Node) (domain : List Location) : Observation := {
  domain := domain
  output := fun loc => match select loc with
    | none => initial .generic loc
    | some writer => (writeByte resolve descriptor c writer loc).getD (initial .generic loc)
  source := fun loc => match select loc with
    | none => none
    | some writer => if (writeByte resolve descriptor c writer loc).isSome then some writer else none
}

theorem race_free_observer_eligible {resolve descriptor c histories cluster rf}
    (hn : ∀ loc a b, ¬ DataRaceAt resolve descriptor c histories cluster rf loc a b) (loc) :
    ObserverEligible resolve descriptor c histories cluster rf loc := by
  constructor
  · rintro ⟨loc,a,b,hr,_⟩; exact hn loc a b hr
  · rintro ⟨a,b,_,_,hr⟩; exact hn loc a b hr

theorem selected_observer {resolve descriptor c initial rf co histories cluster select domain}
    (hd : Complete c) (hg : ∀ loc ∈ domain, loc.space = .global)
    (hc : ∀ writer loc value, loc.space = .global → writeByte resolve descriptor c writer loc = some value → loc ∈ domain)
    (hs : ∀ loc ∈ domain, ∀ writer value, writeByte resolve descriptor c writer loc = some value → select loc = some writer)
    (hi : ∀ loc source, ¬ co loc source source) :
    ObserverConditions resolve descriptor c initial rf co histories cluster (selectedObservation resolve descriptor c initial select domain) := by
  refine ⟨hd,hg,hc,?_,?_⟩
  · intro loc _ _
    cases hsel : select loc with
    | none => simp [selectedObservation,observerValue,hsel]
    | some writer => cases hw : writeByte resolve descriptor c writer loc <;> simp [selectedObservation,observerValue,hsel,hw]
  · intro loc hloc _ writer value hw hco
    have hsel := hs loc hloc writer value hw
    have he : (selectedObservation resolve descriptor c initial select domain).source loc = some writer := by
      simp [selectedObservation,hsel,hw]
    rw [he] at hco
    exact hi loc (some writer) hco

theorem observer_unwritten {resolve descriptor c initial rf co histories cluster o loc}
    (ho : ObserverConditions resolve descriptor c initial rf co histories cluster o)
    (hd : loc ∈ o.domain) (he : ObserverEligible resolve descriptor c histories cluster rf loc)
    (hn : ∀ writer, writeByte resolve descriptor c writer loc = none) : o.output loc = initial .generic loc := by
  have hv := ho.agreement loc hd he
  cases hs : o.source loc with
  | none => exact (Option.some.inj (by simpa [observerValue,hs] using hv)).symm
  | some writer => simp [observerValue,hs,hn] at hv

theorem observer_unique_writer {resolve descriptor c initial rf co histories cluster o loc writer value}
    (hc : CausalConstraints resolve descriptor c initial rf co histories cluster)
    (ho : ObserverConditions resolve descriptor c initial rf co histories cluster o)
    (hd : loc ∈ o.domain) (he : ObserverEligible resolve descriptor c histories cluster rf loc)
    (hw : writeByte resolve descriptor c writer loc = some value)
    (hu : ∀ other v, writeByte resolve descriptor c other loc = some v → other = writer) : o.output loc = value := by
  have hv := ho.agreement loc hd he
  cases hs : o.source loc with
  | none => exact (ho.noStale loc hd he.1 writer value hw (by simpa [hs] using hc.initialization he.1 writer loc value hw)).elim
  | some other =>
    have ha : writeByte resolve descriptor c other loc = some (o.output loc) := by simpa [observerValue,hs] using hv
    have hid := hu other (o.output loc) ha
    subst other
    exact Option.some.inj (ha.symm.trans hw)

end
end Ptx.Hopper.Access
