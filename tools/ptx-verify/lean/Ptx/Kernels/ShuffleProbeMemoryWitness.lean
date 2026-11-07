import Ptx.Kernels.ShuffleProbeLayout

/-! Actual ordinary-memory/observer witnesses for the same complete collective
source candidate. Read-free source traces and disjoint output bytes discharge
the existing weak-memory predicates; no new consistency assumption is added. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

theorem no_memory_barrier_returns {mode input launch candidate actual bid generation}
    (hp : Params input launch.params) (hw : Shuffle.WellFormed (code mode) launch candidate)
    (hc : Shuffle.Complete candidate) : candidate.view.eventAt actual ≠ some (.barrierReturn bid generation) := by
  intro he
  obtain ⟨_,_,_,⟨_,hk⟩ | ⟨_,hk⟩⟩ := actual_memory_event_shape hp hw hc he
  all_goals cases hk

theorem ordinary_memory_witness {mode input launch candidate} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (hl : LayoutPre input launch) :
    Ptx.Event.GenericMemoryConditions candidate.view launch.initial (fun _ _ => .initial) (Ptx.Event.InitialCo candidate.view) := by
  apply Ptx.Event.initial_co_conditions (fun actual => actual.serial)
  · intro a b hp; exact hp.2.2.2
  · rintro a b ⟨_,bid,generation,_,hret⟩
    exact False.elim (no_memory_barrier_returns hp hw hc hret)
  · rintro a b ⟨_,t,_,_,_,bid,generation,hret,_⟩
    exact False.elim (no_memory_barrier_returns hp hw hc hret)
  · intro actual bid generation hret
    exact False.elim (no_memory_barrier_returns hp hw hc hret)
  · intro loc a b va vb ha hb
    exact unique_byte_writer hp hw hc hl ha hb
  · intro read loc value hr
    simp [no_ordinary_reads hp hw hc] at hr
  · intro read writer loc vr vw hr
    simp [no_ordinary_reads hp hw hc] at hr
  · intro read writer loc vr vw hr
    simp [no_ordinary_reads hp hw hc] at hr

theorem exported_kernel_nonvacuous (mode : Mode) (input : Inputs) (domain : Scalar.Launch → List Location)
    (hg : ∀ launch, KernelPre mode input launch → ∀ loc ∈ domain launch, loc.space = .global) :
    Shuffle.Nonvacuous (code mode) (KernelPre mode input) domain := by
  intro launch hp
  let candidate := witnessCandidate mode input launch
  have hw := witness_well_formed mode input launch hp.1.1 hp.1.2.1
  have hc := witness_complete mode input launch
  have hm := ordinary_memory_witness hp.1.2.1 hw hc hp.2
  have ho := Ptx.Event.unique_writers_observation (initial := launch.initial) (rf := fun _ _ => .initial)
    (Shuffle.view_complete hc) (hg launch hp)
    (fun _ _ _ _ _ ha hb => unique_byte_writer hp.1.2.1 hw hc hp.2 ha hb)
  exact ⟨candidate,(fun _ _ => .initial),Ptx.Event.InitialCo candidate.view,
    Ptx.Event.selectedObservation candidate.view launch.initial (Ptx.Event.writerSelector candidate.view) (domain launch),hw,hc,
    all_completed_control_admitted hp.1.2.1 hw hc,all_completed_defined hp.1.2.1 hp.1.2.2 hw hc,
    witness_agreement mode input launch hp.1.1 hp.1.2.1,hm,ho,rfl⟩

end
end Ptx.Kernels.ShuffleProbe
