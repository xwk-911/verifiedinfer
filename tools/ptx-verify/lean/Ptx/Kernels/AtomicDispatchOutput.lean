import Ptx.Kernels.AtomicDispatchCounter

/-! Universal counter/job-output and frame contract for every completed source
candidate admitted by the current memory/observer projection. Global nonvacuity,
physical allocation/runtime and full PTX correspondence are separate duties. -/
namespace Ptx.AtomicDispatchEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

def Covers (cfg : Config) (domain : List Location) : Prop :=
  ∀ base, Cell cfg base → ∀ offset, offset < 4 → base.add offset ∈ domain

theorem counter_output (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Pre cfg launch) (hm : GenericMemoryConditions execution launch.initial rf co)
    (ho : ObserverConditions execution launch.initial rf co o) (jobs : Assignment execution)
    (hc : Covers cfg o.domain) : RepresentsU32 o.output (counterLoc cfg) 2 := by
  intro offset hoff
  apply observer_latest_writer hm ho (hc _ (Or.inl rfl) offset hoff)
    (counter_observer_eligible cfg hw hd hp.1 hp.2.1 rf (counter_offset cfg hoff))
    (second_counter_byte cfg hw hd hp.2.1 jobs hoff)
  intro other value hwrite
  rcases counter_writer_pair cfg hw hd hp.1 hp.2.1 jobs (counter_offset cfg hoff) hwrite with he | he
  · subst other
    exact Or.inr (counter_order cfg hw hd hp hm jobs hoff)
  · exact Or.inl he

theorem x_output (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Pre cfg launch) (hm : GenericMemoryConditions execution launch.initial rf co)
    (ho : ObserverConditions execution launch.initial rf co o) (jobs : Assignment execution)
    (hc : Covers cfg o.domain) : RepresentsU32 o.output (xLoc cfg) 1 := by
  intro offset hoff
  have hl : InWords cfg.x 1 ((xLoc cfg).add offset) := cell_offset rfl hoff
  apply observer_unique_writer hm ho (hc _ (Or.inr (Or.inl rfl)) offset hoff)
    (x_observer_eligible cfg hw hd hp.1 hp.2.1 jobs rf hl) (x_write_byte cfg hw hd hp.2.1 jobs hoff)
  intro other value hwrite
  exact unique_x_writer cfg hw hd hp.2.1 jobs hl hwrite

theorem y_output (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Pre cfg launch) (hm : GenericMemoryConditions execution launch.initial rf co)
    (ho : ObserverConditions execution launch.initial rf co o) (jobs : Assignment execution)
    (hc : Covers cfg o.domain) : RepresentsU32 o.output (yLoc cfg) 2 := by
  intro offset hoff
  have hl : InWords cfg.y 1 ((yLoc cfg).add offset) := cell_offset rfl hoff
  apply observer_unique_writer hm ho (hc _ (Or.inr (Or.inr rfl)) offset hoff)
    (y_observer_eligible cfg hw hd hp.1 hp.2.1 jobs rf hl) (y_write_byte cfg hw hd hp.2.1 jobs hoff)
  intro other value hwrite
  exact unique_y_writer cfg hw hd hp.2.1 jobs hl hwrite

theorem frame_output (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Pre cfg launch) (ho : ObserverConditions execution launch.initial rf co o) (jobs : Assignment execution)
    {loc : Location} (hmem : loc ∈ o.domain)
    (hc : ¬ InWords cfg.counter 1 loc) (hx : ¬ InWords cfg.x 1 loc) (hy : ¬ InWords cfg.y 1 loc) :
    o.output loc = launch.initial loc := by
  have hn := outside_unwritten cfg hw hd hp.2.1 jobs hc hx hy
  apply observer_unwritten ho hmem _ hn
  refine ⟨no_mixed cfg hw hd hp.1 hp.2.1 rf,?_⟩
  rintro ⟨a,b,ha,_,_⟩
  simp [hn a] at ha

theorem correct (cfg : Config) (domain : List Location) (hc : Covers cfg domain) :
    Scalar.Triple code (Pre cfg) (fun _ => domain) (fun launch output => Post cfg launch.initial output domain) := by
  intro launch execution rf co o hp hw hm ho hdomain
  obtain ⟨jobs⟩ := assignment cfg hw ho.complete hp hm
  have hcover : Covers cfg o.domain := hdomain ▸ hc
  refine ⟨counter_output cfg hw ho.complete hp hm ho jobs hcover,
    x_output cfg hw ho.complete hp hm ho jobs hcover,y_output cfg hw ho.complete hp hm ho jobs hcover,?_⟩
  intro loc hmem hcounter hx hy
  exact frame_output cfg hw ho.complete hp ho jobs (hdomain ▸ hmem) hcounter hx hy

end
end Ptx.AtomicDispatchEvent
