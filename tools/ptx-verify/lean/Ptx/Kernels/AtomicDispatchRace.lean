import Ptx.Kernels.AtomicDispatchOutputMemory

/-! Race exclusion from a source-checked job assignment. The assignment can
either be derived for universal correctness or constructed for one witness;
this rule does not assume memory consistency. -/
namespace Ptx.AtomicDispatchEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

theorem read_region (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    {read loc value} (hr : execution.readByte read loc = some value) : InWords cfg.counter 1 loc := by
  obtain ⟨reply,_,hpayload⟩ := read_shape cfg hw hd hg hp hr
  have hb := payloadByte_bounds hpayload
  rw [u32_bytes_size] at hb
  exact ⟨hb.1.symm,hb.2.1,by simpa only [counterLoc,Nat.mul_one] using hb.2.2⟩

theorem counter_reader_pair (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params) (jobs : Assignment execution)
    {read loc value} (hr : execution.readByte read loc = some value) :
    read = firstCounter jobs ∨ read = secondCounter jobs := by
  have hl := read_region cfg hw hd hg hp hr
  obtain ⟨v,hserial,he⟩ := counter_access cfg hw hd hg hp hl (Or.inl (by rw [hr]; rfl))
  obtain ⟨t,ht,hid,_⟩ := eventAt_trace he
  rcases jobs.covers t ht with rfl | rfl
  · exact Or.inl (by cases read; simp_all [firstCounter])
  · exact Or.inr (by cases read; simp_all [secondCounter])

theorem x_access_write (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    {event loc} (hl : InWords cfg.x 1 loc) (ha : execution.Accesses event loc) : ∃ value, execution.writeByte event loc = some value := by
  rcases ha with hr | hwri
  · obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp hr
    exact (words_disjoint cfg.counterX (read_region cfg hw hd hg hp hv) hl).elim
  · exact Option.isSome_iff_exists.mp hwri

theorem y_access_write (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    {event loc} (hl : InWords cfg.y 1 loc) (ha : execution.Accesses event loc) : ∃ value, execution.writeByte event loc = some value := by
  rcases ha with hr | hwri
  · obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp hr
    exact (words_disjoint cfg.counterY (read_region cfg hw hd hg hp hv) hl).elim
  · exact Option.isSome_iff_exists.mp hwri

theorem no_races_of_assignment (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    (jobs : Assignment execution) (rf : ReadsFrom) (a b : EventId) : ¬ DataRace execution rf a b := by
  intro hr
  obtain ⟨loc,ha,hb⟩ := hr.overlap
  obtain ⟨base,hcell,hf⟩ := event_footprint cfg hw hd hg hp (accesses_present ha)
  have hbounds := access_footprint_bounds ha hf
  have hl : InWords base.address 1 loc :=
    ⟨hbounds.1.symm.trans (cell_global hcell),hbounds.2.1,by simpa only [Nat.mul_one] using hbounds.2.2⟩
  rcases hcell with rfl | rfl | rfl
  · exact counter_no_race cfg hw hd hg hp rf hl ha hb hr
  · obtain ⟨va,hwa⟩ := x_access_write cfg hw hd hg hp hl ha
    obtain ⟨vb,hwb⟩ := x_access_write cfg hw hd hg hp hl hb
    have he := (unique_x_writer cfg hw hd hp jobs hl hwa).trans (unique_x_writer cfg hw hd hp jobs hl hwb).symm
    subst b
    exact hr.notStrong (write_self_strong hwa)
  · obtain ⟨va,hwa⟩ := y_access_write cfg hw hd hg hp hl ha
    obtain ⟨vb,hwb⟩ := y_access_write cfg hw hd hg hp hl hb
    have he := (unique_y_writer cfg hw hd hp jobs hl hwa).trans (unique_y_writer cfg hw hd hp jobs hl hwb).symm
    subst b
    exact hr.notStrong (write_self_strong hwa)

theorem no_returns (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    (event : EventId) (bid generation : Nat) : execution.eventAt event ≠ some (.barrierReturn bid generation) := by
  intro he
  obtain ⟨_,_,hs⟩ := event_shape cfg hw hd hg hp he
  rcases hs with ⟨_,hk⟩ | ⟨_,_,hk⟩ | ⟨_,_,hk⟩ <;> cases hk

end
end Ptx.AtomicDispatchEvent
