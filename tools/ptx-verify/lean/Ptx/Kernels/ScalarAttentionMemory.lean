import Ptx.Kernels.ScalarAttentionEvents

/-! Race freedom and immutable-input eligibility derived from source events and
layout, not assumed by the precondition or by the general weak memory model. -/
namespace Ptx.ScalarAttentionEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarAttention
noncomputable section

theorem input_unwritten {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {loc : Location} (hi : InInput cfg loc) (writer : EventId) : execution.writeByte writer loc = none := by
  cases he : execution.writeByte writer loc with
  | none => rfl
  | some value =>
    have hout := write_region hw hd hg hp he
    have hl := cfg.readLayout hi.1
    rcases hi.2 with hs | hq | hk | hv
    · exact (words_disjoint hl.separateScale hs hout).elim
    · exact (words_disjoint hl.separateQ hq hout).elim
    · exact (words_disjoint hl.separateKey hk hout).elim
    · exact (words_disjoint hl.separateValue hv hout).elim

theorem overlapping_writers_equal {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {a b : EventId} {loc : Location} {va vb : Symbolic.Byte}
    (ha : execution.writeByte a loc = some va) (hb : execution.writeByte b loc = some vb) : a = b := by
  obtain ⟨hva,haa,hsa,x,hpa⟩ := write_shape hw hd hg hp ha
  obtain ⟨hvb,hbb,hsb,y,hpb⟩ := write_shape hw hd hg hp hb
  have hba := payloadByte_bounds hpa
  have hbbounds := payloadByte_bounds hpb
  simp only [outputLoc,Symbolic.encode_length,Symbolic.Format.bytes] at hba hbbounds
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
  rcases hs with ⟨_,_,_,_,hk⟩ | ⟨_,hk⟩ <;> cases hk

theorem no_races {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (rf : ReadsFrom) (a b : EventId) : ¬ DataRace execution rf a b := by
  intro h
  obtain ⟨loc,ha,hb⟩ := h.overlap
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · obtain ⟨va,hra⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hrb⟩ := Option.isSome_iff_exists.mp hb
    rcases h.conflict with ⟨other,value,hwrite⟩ | ⟨other,value,hwrite⟩
    · exact read_write_exclusive (no_rmw hw hd hg hp a) hra hwrite
    · exact read_write_exclusive (no_rmw hw hd hg hp b) hrb hwrite
  · obtain ⟨va,hra⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hwb⟩ := Option.isSome_iff_exists.mp hb
    have hn := input_unwritten hw hd hg hp (read_region hw hd hg hp hra) b
    rw [hn] at hwb
    cases hwb
  · obtain ⟨va,hwa⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hrb⟩ := Option.isSome_iff_exists.mp hb
    have hn := input_unwritten hw hd hg hp (read_region hw hd hg hp hrb) a
    rw [hn] at hwa
    cases hwa
  · obtain ⟨va,hwa⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨vb,hwb⟩ := Option.isSome_iff_exists.mp hb
    have he := overlapping_writers_equal hw hd hg hp hwa hwb
    subst b
    exact h.notStrong (write_self_strong hwa)

theorem outside_unwritten {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {loc : Location} (ho : ¬ InWords cfg.input.output (cfg.input.m*cfg.input.dim) loc) (writer : EventId) :
    execution.writeByte writer loc = none := by
  cases he : execution.writeByte writer loc with
  | none => rfl
  | some value => exact (ho (write_region hw hd hg hp he)).elim

end
end Ptx.ScalarAttentionEvent
