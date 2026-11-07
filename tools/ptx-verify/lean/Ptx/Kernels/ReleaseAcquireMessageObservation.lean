import Ptx.Kernels.ReleaseAcquireMessageMemory
import Ptx.Ordered.Observation
import Ptx.Event.AlignedWords

/-! Final synchronized observation joined to the same complete source/memory
witness. Correctness here quantifies over observations of this actual candidate;
arbitrary completed source candidates and finite polling prefixes remain the
separate universal-kernel obligation. -/
namespace Ptx.Kernels.ReleaseAcquireMessage
open Ptx.ISA
noncomputable section

def domain : List Location := (List.range 264).map (fun address => ⟨.global,address⟩)
def Written (loc : Location) : Prop := loc.space = .global ∧
  ((64 ≤ loc.address ∧ loc.address < 68) ∨ (128 ≤ loc.address ∧ loc.address < 132) ∨ (256 ≤ loc.address ∧ loc.address < 260))
def Post (initial final : Scalar.ByteMap) : Prop :=
  Scalar.RepresentsU32 final payload 42 ∧ Scalar.RepresentsU32 final flag 1 ∧ Scalar.RepresentsU32 final output 42 ∧
    ∀ loc ∈ domain, ¬Written loc → final loc = initial loc

theorem domain_global : ∀ loc ∈ domain, loc.space = .global := by
  intro loc hl
  obtain ⟨address,_,rfl⟩ := List.mem_map.mp hl
  rfl

theorem domain_covers_words {base : Location} (hb : base = payload ∨ base = flag ∨ base = output)
    {offset : Nat} (ho : offset < 4) : base.add offset ∈ domain := by
  rcases hb with rfl | rfl | rfl
  all_goals
    apply List.mem_map.mpr
    refine ⟨_,List.mem_range.mpr ?_,rfl⟩
    simp only [payload,flag,output,Location.add]
    omega

theorem actual_word_footprint {event} (he : candidate.view.Present event) :
    ∃ base, (candidate.view.eventAt event).bind Ptx.Event.Kind.footprint = some (base,4) ∧ base.address % 4 = 0 := by
  obtain ⟨kind,hkind⟩ := Option.isSome_iff_exists.mp he
  obtain ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ := view_event_cases hkind
  · exact ⟨payload,by simp only [hkind,Option.bind_some,Ptx.Event.Kind.footprint,Scalar.u32_bytes_size],by decide⟩
  · exact ⟨flag,by simp only [hkind,Option.bind_some,Ptx.Event.Kind.footprint,Scalar.u32_bytes_size],by decide⟩
  · exact ⟨flag,by simp only [hkind,Option.bind_some,Ptx.Event.Kind.footprint,Scalar.u32_bytes_size],by decide⟩
  · exact ⟨payload,by simp only [hkind,Option.bind_some,Ptx.Event.Kind.footprint,Scalar.u32_bytes_size],by decide⟩
  · exact ⟨output,by simp only [hkind,Option.bind_some,Ptx.Event.Kind.footprint,Scalar.u32_bytes_size],by decide⟩

theorem no_mixed_size_races (sources : Ptx.Event.ReadsFrom) : ¬Ordered.MixedSizeRace candidate sources := by
  rintro ⟨a,b,hr,hn⟩
  obtain ⟨loc,ha,hb⟩ := hr.overlap
  obtain ⟨base,hbase,halign⟩ := actual_word_footprint (Ptx.Event.accesses_present ha)
  obtain ⟨other,hother,hbalign⟩ := actual_word_footprint (Ptx.Event.accesses_present hb)
  have he := Ptx.Event.overlapping_aligned_words_same_base hbase hother halign hbalign hr.overlap
  exact hn ⟨(base,4),hbase,he ▸ hother⟩

theorem observer_eligible (sources : Ptx.Event.ReadsFrom) (loc : Location) : Ordered.ObserverEligible candidate sources loc :=
  Ordered.unique_byte_observer_eligible (no_mixed_size_races sources) (fun _ _ _ _ ha hb => unique_byte_writer ha hb)

theorem outside_written_has_no_writer {loc} (hout : ¬Written loc) : ∀ writer, candidate.view.writeByte writer loc = none := by
  intro writer
  cases hw : candidate.view.writeByte writer loc with
  | none => rfl
  | some value =>
    obtain ⟨_,hbyte⟩ | ⟨_,hbyte⟩ | ⟨_,hbyte⟩ := write_cases hw
    all_goals
      have hb := Ptx.Event.payloadByte_bounds hbyte
      simp only [payload,flag,output,Scalar.u32_bytes_size] at hb
      apply False.elim
      apply hout
      unfold Written
      exact ⟨hb.1.symm,by omega⟩

theorem all_observers_of_actual_candidate_correct {initial sources co observation}
    (hm : Ordered.MemoryConditions candidate initial sources co)
    (ho : Ordered.ObserverConditions candidate initial sources co observation) (hd : observation.domain = domain) :
    Post initial observation.output := by
  have hu : ∀ writer base value, candidate.view.eventAt writer = some (.write base (Scalar.u32Bytes value)) →
      (base = payload ∨ base = flag ∨ base = output) → Scalar.RepresentsU32 observation.output base value := by
    intro writer base value hw hb
    apply Ordered.observe_u32_write hm ho hw
    · intro offset hoffset
      rw [hd]
      exact domain_covers_words hb hoffset
    · exact fun _ _ => observer_eligible sources _
    · intro offset hoffset other otherValue hother
      have hown : candidate.view.writeByte writer (base.add offset) = some (Scalar.u32Byte value offset) := by
        simpa only [Ptx.Event.Candidate.writeByte,hw,Option.bind_some,Ptx.Event.Kind.writeByte]
          using Scalar.u32_payload_byte base value offset hoffset
      exact unique_byte_writer hother hown
  refine ⟨hu payloadWrite payload 42 rfl (Or.inl rfl),hu flagWrite flag 1 rfl (Or.inr (Or.inl rfl)),
    hu outputWrite output 42 rfl (Or.inr (Or.inr rfl)),?_⟩
  intro loc hl hout
  apply Ordered.observer_unwritten ho _ (observer_eligible sources loc) (outside_written_has_no_writer hout)
  simpa only [hd] using hl

def SourcePre (actualLaunch : Scalar.Launch) : Prop := actualLaunch.geometry = launch.geometry ∧ actualLaunch.params = bindings

theorem source_well_formed_for_initial {actualLaunch} (hp : SourcePre actualLaunch) :
    Ordered.WellFormed code actualLaunch candidate := by
  rcases actualLaunch with ⟨geometry,params,initial⟩
  rcases hp with ⟨rfl,rfl⟩
  exact source_candidate_is_well_formed

theorem nonvacuous : Ordered.Nonvacuous code SourcePre (fun _ => domain) := by
  intro actualLaunch hp
  exact ⟨candidate,rf,Ptx.Event.InitialCo candidate.view,
    Ptx.Event.selectedObservation candidate.view actualLaunch.initial (Ptx.Event.writerSelector candidate.view) domain,
    source_well_formed_for_initial hp,source_candidate_is_complete,actual_memory_consistent actualLaunch.initial,
    Ordered.unique_writers_observation source_candidate_is_complete domain_global
      (fun _ _ _ _ _ ha hb => unique_byte_writer ha hb),rfl⟩

theorem complete_observed_execution (actualLaunch : Scalar.Launch) (hp : SourcePre actualLaunch) :
    ∃ execution sources co observation, Ordered.WellFormed code actualLaunch execution ∧ Ordered.Complete execution ∧
      Ordered.MemoryConditions execution actualLaunch.initial sources co ∧
      Ordered.ObserverConditions execution actualLaunch.initial sources co observation ∧ observation.domain = domain ∧
      Post actualLaunch.initial observation.output := by
  let observation := Ptx.Event.selectedObservation candidate.view actualLaunch.initial (Ptx.Event.writerSelector candidate.view) domain
  have hm := actual_memory_consistent actualLaunch.initial
  have ho : Ordered.ObserverConditions candidate actualLaunch.initial rf (Ptx.Event.InitialCo candidate.view) observation :=
    Ordered.unique_writers_observation source_candidate_is_complete domain_global (fun _ _ _ _ _ ha hb => unique_byte_writer ha hb)
  exact ⟨candidate,rf,Ptx.Event.InitialCo candidate.view,observation,source_well_formed_for_initial hp,
    source_candidate_is_complete,hm,ho,rfl,all_observers_of_actual_candidate_correct hm ho rfl⟩

end
end Ptx.Kernels.ReleaseAcquireMessage
