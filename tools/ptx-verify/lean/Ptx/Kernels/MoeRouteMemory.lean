import Ptx.Kernels.MoeRouteEvents
import Ptx.Event.ReadOnlyInputs

/-! Gate immutability, unique route writers and race freedom are derived from
the actual source events and declared live regions, not caller assumptions. -/
namespace Ptx.MoeRouteEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeRouteThread
noncomputable section

theorem input_unwritten {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {loc : Location} (hi : InWords cfg.input.g (2*cfg.input.m) loc) (writer : EventId) :
    execution.writeByte writer loc = none := by
  cases he : execution.writeByte writer loc with
  | none => rfl
  | some value => exact (words_disjoint cfg.separate hi (write_region hw hd hg hp he)).elim

theorem overlapping_writers_equal {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {a b : EventId} {loc : Location} {va vb : Symbolic.Byte}
    (ha : execution.writeByte a loc = some va) (hb : execution.writeByte b loc = some vb) : a = b := by
  obtain ⟨hva,haa,hsa,x,hpa⟩ := write_shape hw hd hg hp ha
  obtain ⟨hvb,hbb,hsb,y,hpb⟩ := write_shape hw hd hg hp hb
  have hba := payloadByte_bounds hpa
  have hbbounds := payloadByte_bounds hpb
  simp only [rLoc,u32_bytes_size] at hba hbbounds
  have hindex := word_index_of_overlap hba.2.1 hba.2.2 hbbounds.2.1 hbbounds.2.2
  have hthread := index_injective cfg hva hvb hindex
  cases a
  cases b
  simp_all

theorem no_rmw {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) (event : EventId) :
    ¬ execution.IsRMW event := by
  rintro ⟨scope,base,bytes,he⟩
  obtain ⟨_,_,_,hs⟩ := event_shape hw hd hg hp he
  rcases hs with ⟨_,hk⟩ | ⟨_,hk⟩ | ⟨_,hk⟩ <;> cases hk

theorem no_races {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (rf : ReadsFrom) (a b : EventId) : ¬ DataRace execution rf a b := by
  apply disjoint_reads_unique_writes_no_races (no_rmw hw hd hg hp)
  · intro read loc value hr writer
    exact input_unwritten hw hd hg hp (read_region hw hd hg hp hr) writer
  · intro loc x y vx vy hx hy
    exact overlapping_writers_equal hw hd hg hp hx hy

theorem outside_unwritten {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {loc : Location} (ho : ¬ InWords cfg.input.r cfg.input.m loc) (writer : EventId) :
    execution.writeByte writer loc = none := by
  cases he : execution.writeByte writer loc with
  | none => rfl
  | some value => exact (ho (write_region hw hd hg hp he)).elim

end
end Ptx.MoeRouteEvent
