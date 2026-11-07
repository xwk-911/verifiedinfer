import Ptx.Kernels.AtomicDispatchAssigned

/-! Unique job writers, untouched frame and byte-observer eligibility, derived
after the ticket assignment. No global race-free launch premise is introduced. -/
namespace Ptx.AtomicDispatchEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

theorem write_word_region {execution : Scalar.Candidate} {writer loc value base}
    (hw : execution.writeByte writer loc = some value)
    (hf : (execution.eventAt writer).bind Kind.footprint = some (base,4)) (hg : base.space = .global) :
    InWords base.address 1 loc := by
  have hb := access_footprint_bounds (Or.inr (by rw [hw]; rfl)) hf
  exact ⟨hb.1.symm.trans hg,hb.2.1,by simpa only [Nat.mul_one] using hb.2.2⟩

theorem unique_x_writer (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution)
    {writer loc value} (hl : InWords cfg.x 1 loc) (hwrite : execution.writeByte writer loc = some value) :
    writer = firstJob jobs := by
  have hi := assigned_inventory cfg hw hd hp jobs (accesses_present (Or.inr (by rw [hwrite]; rfl)))
  have hf := assigned_footprints cfg hw hd hp jobs
  rcases hi with rfl | rfl | rfl | rfl
  · exact (words_disjoint cfg.counterX (write_word_region hwrite hf.1 rfl) hl).elim
  · rfl
  · exact (words_disjoint cfg.counterX (write_word_region hwrite hf.2.2.1 rfl) hl).elim
  · exact (words_disjoint cfg.xy hl (write_word_region hwrite hf.2.2.2 rfl)).elim

theorem unique_y_writer (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution)
    {writer loc value} (hl : InWords cfg.y 1 loc) (hwrite : execution.writeByte writer loc = some value) :
    writer = secondJob jobs := by
  have hi := assigned_inventory cfg hw hd hp jobs (accesses_present (Or.inr (by rw [hwrite]; rfl)))
  have hf := assigned_footprints cfg hw hd hp jobs
  rcases hi with rfl | rfl | rfl | rfl
  · exact (words_disjoint cfg.counterY (write_word_region hwrite hf.1 rfl) hl).elim
  · exact (words_disjoint cfg.xy (write_word_region hwrite hf.2.1 rfl) hl).elim
  · exact (words_disjoint cfg.counterY (write_word_region hwrite hf.2.2.1 rfl) hl).elim
  · rfl

theorem outside_unwritten (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution)
    {loc : Location} (hc : ¬ InWords cfg.counter 1 loc) (hx : ¬ InWords cfg.x 1 loc) (hy : ¬ InWords cfg.y 1 loc)
    (writer : EventId) : execution.writeByte writer loc = none := by
  cases he : execution.writeByte writer loc with
  | none => rfl
  | some value =>
    have hi := assigned_inventory cfg hw hd hp jobs (accesses_present (Or.inr (by rw [he]; rfl)))
    have hf := assigned_footprints cfg hw hd hp jobs
    rcases hi with rfl | rfl | rfl | rfl
    · exact (hc (write_word_region he hf.1 rfl)).elim
    · exact (hx (write_word_region he hf.2.1 rfl)).elim
    · exact (hc (write_word_region he hf.2.2.1 rfl)).elim
    · exact (hy (write_word_region he hf.2.2.2 rfl)).elim

theorem x_observer_eligible (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    (jobs : Assignment execution) (rf : ReadsFrom) {loc : Location} (hl : InWords cfg.x 1 loc) :
    ObserverEligible execution rf loc := by
  apply unique_byte_observer_eligible (no_mixed cfg hw hd hg hp rf)
  intro a b va vb ha hb
  exact (unique_x_writer cfg hw hd hp jobs hl ha).trans (unique_x_writer cfg hw hd hp jobs hl hb).symm

theorem y_observer_eligible (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    (jobs : Assignment execution) (rf : ReadsFrom) {loc : Location} (hl : InWords cfg.y 1 loc) :
    ObserverEligible execution rf loc := by
  apply unique_byte_observer_eligible (no_mixed cfg hw hd hg hp rf)
  intro a b va vb ha hb
  exact (unique_y_writer cfg hw hd hp jobs hl ha).trans (unique_y_writer cfg hw hd hp jobs hl hb).symm

theorem counter_observer_eligible (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    (rf : ReadsFrom) {loc : Location} (hl : InWords cfg.counter 1 loc) : ObserverEligible execution rf loc := by
  refine ⟨no_mixed cfg hw hd hg hp rf,?_⟩
  rintro ⟨a,b,ha,hb,hr⟩
  exact counter_no_race cfg hw hd hg hp rf hl (Or.inr ha) (Or.inr hb) hr

theorem cell_offset {base : Location} (hg : base.space = .global) {offset : Nat} (ho : offset < 4) :
    InWords base.address 1 (base.add offset) := by
  exact ⟨hg,by simp [Location.add],by simp only [Location.add,Nat.mul_one]; omega⟩

theorem x_write_byte (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution)
    {offset : Nat} (ho : offset < 4) : execution.writeByte (firstJob jobs) ((xLoc cfg).add offset) = some (u32Byte 1 offset) := by
  simpa only [Candidate.writeByte,assigned_x_event cfg hw hd hp jobs,Option.bind_some,Kind.writeByte]
    using u32_payload_byte (xLoc cfg) 1 offset ho

theorem y_write_byte (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution)
    {offset : Nat} (ho : offset < 4) : execution.writeByte (secondJob jobs) ((yLoc cfg).add offset) = some (u32Byte 2 offset) := by
  simpa only [Candidate.writeByte,assigned_y_event cfg hw hd hp jobs,Option.bind_some,Kind.writeByte]
    using u32_payload_byte (yLoc cfg) 2 offset ho

end
end Ptx.AtomicDispatchEvent
