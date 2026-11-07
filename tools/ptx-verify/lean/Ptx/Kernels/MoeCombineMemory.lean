import Ptx.Kernels.MoeCombineEvents
import Ptx.Event.ReadOnlyInputs

/-! Program-specific separation, writer uniqueness and race freedom, derived
from actual candidates. Racing executions remain in the general memory model.
-/
namespace Ptx.MoeCombineEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeCombine
noncomputable section

theorem input_unwritten {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {loc : Location} (hi : InWords cfg.input.r (cfg.input.m) loc ∨
      InWords cfg.input.h ((2*cfg.input.m)*cfg.input.n) loc) (writer : EventId) : execution.writeByte writer loc = none := by
  cases he : execution.writeByte writer loc with
  | none => rfl
  | some value =>
    have hc := write_region hw hd hg hp he
    exact (hi.elim (fun ha => words_disjoint cfg.separateR ha hc) (fun hb => words_disjoint cfg.separateH hb hc)).elim

theorem overlapping_writers_equal {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {a b : EventId} {loc : Location} {va vb : Symbolic.Byte}
    (ha : execution.writeByte a loc = some va) (hb : execution.writeByte b loc = some vb) : a = b := by
  obtain ⟨hva,haa,hsa,x,hpa⟩ := write_shape hw hd hg hp ha
  obtain ⟨hvb,hbb,hsb,y,hpb⟩ := write_shape hw hd hg hp hb
  have hba := payloadByte_bounds hpa
  have hbbounds := payloadByte_bounds hpb
  simp only [yLoc,Symbolic.encode_length,Symbolic.Format.bytes] at hba hbbounds
  have hindex := word_index_of_overlap hba.2.1 hba.2.2 hbbounds.2.1 hbbounds.2.2
  have hcoords := matrix_index_injective haa.2 hbb.2 hindex
  have hthread := output_coordinates_injective cfg.gridZ cfg.blockZ hva hvb hcoords.1 hcoords.2
  cases a
  cases b
  simp_all

theorem no_rmw {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) (event : EventId) :
    ¬ execution.IsRMW event := by
  rintro ⟨scope,base,bytes,he⟩
  obtain ⟨_,_,_,hs⟩ := event_shape hw hd hg hp he
  rcases hs with ⟨_,hk⟩ | ⟨_,⟨_,hk⟩ | ⟨_,hk⟩⟩ <;> cases hk

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
    {loc : Location} (ho : ¬ InWords cfg.input.y (cfg.input.m*cfg.input.n) loc) (writer : EventId) :
    execution.writeByte writer loc = none := by
  cases he : execution.writeByte writer loc with
  | none => rfl
  | some value => exact (ho (write_region hw hd hg hp he)).elim

end
end Ptx.MoeCombineEvent
