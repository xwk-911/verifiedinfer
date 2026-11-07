import Ptx.Kernels.ReleaseAcquireMessageObservation

/-! A complete source/memory/observer witness, independent output/guard checks
and rejection of stale payload or observer sources. Universal loop correctness
is deliberately not inferred from this one constructed candidate. -/
namespace Ptx.OrderedWitnessTests
open Ptx.ISA Ptx.Kernels.ReleaseAcquireMessage
noncomputable section

theorem actual_memory_witness_for_arbitrary_initial (initial : Scalar.ByteMap) :
    Ordered.MemoryConditions candidate initial rf (Ptx.Event.InitialCo candidate.view) := actual_memory_consistent initial

theorem full_observed_execution_exists :
    ∃ execution sources co observation, Ordered.WellFormed code launch execution ∧ Ordered.Complete execution ∧
      Ordered.MemoryConditions execution launch.initial sources co ∧
      Ordered.ObserverConditions execution launch.initial sources co observation ∧ observation.domain = domain ∧
      Post launch.initial observation.output := complete_observed_execution launch ⟨rfl,rfl⟩

def nonzeroLaunch : Scalar.Launch := {launch with initial := fun _ => .bits (byte 99)}
theorem initially_nonzero_observed_execution_exists :
    ∃ execution sources co observation, Ordered.WellFormed code nonzeroLaunch execution ∧ Ordered.Complete execution ∧
      Ordered.MemoryConditions execution nonzeroLaunch.initial sources co ∧
      Ordered.ObserverConditions execution nonzeroLaunch.initial sources co observation ∧ observation.domain = domain ∧
      Post nonzeroLaunch.initial observation.output := complete_observed_execution nonzeroLaunch ⟨rfl,rfl⟩

theorem independent_output_byte {initial final} (hp : Post initial final) : final output = Scalar.u32Byte 42 0 := by
  simpa only [Location.add,Nat.add_zero] using hp.2.2.1 0 (by decide)

theorem independent_guards {initial final} (hp : Post initial final) :
    final ⟨.global,63⟩ = initial ⟨.global,63⟩ ∧ final ⟨.global,260⟩ = initial ⟨.global,260⟩ := by
  constructor
  · apply hp.2.2.2 _ (List.mem_map.mpr ⟨63,List.mem_range.mpr (by decide),rfl⟩)
    norm_num [Written]
  · apply hp.2.2.2 _ (List.mem_map.mpr ⟨260,List.mem_range.mpr (by decide),rfl⟩)
    norm_num [Written]

def staleSources : Ptx.Event.ReadsFrom := fun read loc => if read = payloadRead then .initial else rf read loc

theorem stale_payload_does_not_remove_flag_synchronization :
    Ordered.ReleaseAcquireSync candidate staleSources flagWrite flagRead := by
  refine ⟨rfl,rfl,flag_endpoints_are_mutually_strong,Ordered.ObservationOrder.direct ?_⟩
  exact ⟨flag_endpoints_are_mutually_strong,flag,Scalar.u32Byte 1 0,rfl,rfl,rfl⟩

theorem stale_payload_source_is_rejected (initial : Scalar.ByteMap) :
    ¬Ordered.MemoryConditions candidate initial staleSources (Ptx.Event.InitialCo candidate.view) := by
  intro hm
  have hw : candidate.view.writeByte payloadWrite payload = some (Scalar.u32Byte 42 0) := rfl
  have hr : candidate.view.readByte payloadRead payload = some (Scalar.u32Byte 42 0) := rfl
  have hc : Ordered.Causality candidate staleSources payloadWrite payloadRead :=
    Or.inl ⟨⟨payload,Or.inr (by rw [hw]; rfl),Or.inl (by rw [hr]; rfl)⟩,
      Ordered.publish_release_acquire producer_payload_precedes_release stale_payload_does_not_remove_flag_synchronization
        consumer_acquire_precedes_payload⟩
  apply (hm.causality (no_mixed_size_races staleSources)).noStale payloadWrite payloadRead payload _ _ hw hr hc
  exact ⟨rfl,payloadWrite,Scalar.u32Byte 42 0,rfl,hw⟩

def initialObserver (initial : Scalar.ByteMap) : Scalar.Observation := ⟨domain,initial,fun _ => .initial⟩

theorem observer_cannot_keep_initial_source (initial : Scalar.ByteMap) :
    ¬Ordered.ObserverConditions candidate initial rf (Ptx.Event.InitialCo candidate.view) (initialObserver initial) := by
  intro ho
  have hw : candidate.view.writeByte outputWrite output = some (Scalar.u32Byte 42 0) := rfl
  have hd : output ∈ (initialObserver initial).domain := List.mem_map.mpr ⟨256,List.mem_range.mpr (by decide),rfl⟩
  apply ho.noStale output hd (no_mixed_size_races rf) outputWrite _ hw
  exact ⟨rfl,outputWrite,Scalar.u32Byte 42 0,rfl,hw⟩

theorem output_and_left_guard_are_distinct : output ≠ (⟨.global,63⟩ : Location) := by decide
theorem observed_domain_includes_output_last_byte : (⟨.global,259⟩ : Location) ∈ domain :=
  List.mem_map.mpr ⟨259,List.mem_range.mpr (by decide),rfl⟩
theorem observed_domain_includes_right_guard : (⟨.global,260⟩ : Location) ∈ domain :=
  List.mem_map.mpr ⟨260,List.mem_range.mpr (by decide),rfl⟩

end
end Ptx.OrderedWitnessTests
