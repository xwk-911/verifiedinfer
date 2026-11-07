import Ptx.Kernels.MoeExpertsEvents
import Ptx.Event.ReadOnlyInputs

/-! Immutable R/X/W and unique expert-plane writers derived before route
agreement. Invalid route candidates cannot bypass the shared memory model. -/
namespace Ptx.MoeExpertsEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeExperts Ptx.MoeExpertsLoop
noncomputable section

theorem input_unwritten {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {loc : Location} (hi : InWords cfg.input.r cfg.input.m loc ∨ InWords cfg.input.x (cfg.input.m*cfg.input.k) loc ∨
      InWords cfg.input.w ((2*cfg.input.k)*cfg.input.n) loc) (writer : EventId) : execution.writeByte writer loc = none := by
  cases he : execution.writeByte writer loc with
  | none => rfl
  | some value =>
    have hout := write_region hw hd hg hp he
    rcases hi with hr | hx | hw
    · exact (words_disjoint cfg.separateR hr hout).elim
    · exact (words_disjoint cfg.separateX hx hout).elim
    · exact (words_disjoint cfg.separateW hw hout).elim

theorem overlapping_writers_equal {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {a b : EventId} {loc : Location} {va vb : Symbolic.Byte}
    (ha : execution.writeByte a loc = some va) (hb : execution.writeByte b loc = some vb) : a = b := by
  obtain ⟨hva,haa,hsa,e,he,x,hpa⟩ := write_shape hw hd hg hp ha
  obtain ⟨hvb,hbb,hsb,f,hf,y,hpb⟩ := write_shape hw hd hg hp hb
  have hba := payloadByte_bounds hpa
  have hbbounds := payloadByte_bounds hpb
  simp only [hLoc,Symbolic.encode_length,Symbolic.Format.bytes] at hba hbbounds
  have hindex := word_index_of_overlap hba.2.1 hba.2.2 hbbounds.2.1 hbbounds.2.2
  obtain ⟨_,hrow,hcol⟩ := Moe.expert_index_injective haa.1 hbb.1 haa.2 hbb.2 hindex
  have hthread := output_coordinates_injective cfg.gridZ cfg.blockZ hva hvb hrow hcol
  cases a
  cases b
  simp_all

theorem no_rmw {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) (event : EventId) :
    ¬ execution.IsRMW event := by
  rintro ⟨scope,base,bytes,he⟩
  obtain ⟨_,_,_,hs⟩ := event_shape hw hd hg hp he
  rcases hs with ⟨_,hk⟩ | ⟨_,⟨_,_,_,hk⟩ | ⟨_,_,_,hk⟩ | ⟨_,hk⟩⟩ <;> cases hk

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
    {loc : Location} (ho : ¬ InWords cfg.input.h ((2*cfg.input.m)*cfg.input.n) loc) (writer : EventId) :
    execution.writeByte writer loc = none := by
  cases he : execution.writeByte writer loc with
  | none => rfl
  | some value => exact (ho (write_region hw hd hg hp he)).elim

end
end Ptx.MoeExpertsEvent
