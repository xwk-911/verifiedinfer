import Ptx.Kernels.ShuffleProbeWitness
import Ptx.Kernels.ShuffleProbeFrame

/-! Single-CTA output layout with explicit extent and u32-index bounds. These
are input/layout requirements, not assumptions about memory-model results. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

structure LayoutPre (input : Inputs) (launch : Scalar.Launch) : Prop where
  grid : launch.geometry.grid = .one
  count : launch.geometry.block.volume ≤ 2^32
  aligned : input.out % 4 = 0
  extent : input.out + 8*launch.geometry.block.volume ≤ 2^64

def KernelPre (mode : Mode) (input : Inputs) (launch : Scalar.Launch) : Prop :=
  SafePre mode input launch ∧ LayoutPre input launch

theorem valid_thread_index_unique {launch : Scalar.Launch} (hg : launch.geometry.Valid)
    (hgrid : launch.geometry.grid = .one) {a b : ThreadId} (ha : a.Valid launch.geometry) (hb : b.Valid launch.geometry)
    (hi : linear launch.geometry.block a = linear launch.geometry.block b) : a = b := by
  have ht : a.tid = b.tid := Dim3.linear_injective hg.2 ha.2 hb.2 hi
  have hca := ha.1
  have hcb := hb.1
  rw [hgrid] at hca hcb
  rcases a with ⟨⟨ax,ay,az⟩,aTid⟩
  rcases b with ⟨⟨bx,byc,bz⟩,bt⟩
  simp only [Dim3.Within,Dim3.one] at hca hcb
  have hax : ax = 0 := by omega
  have hay : ay = 0 := by omega
  have haz : az = 0 := by omega
  have hbx : bx = 0 := by omega
  have hby : byc = 0 := by omega
  have hbz : bz = 0 := by omega
  subst ax; subst ay; subst az; subst bx; subst byc; subst bz
  dsimp only at ht
  subst bt
  rfl

theorem output_location_layout {input : Inputs} {launch : Scalar.Launch} (hg : launch.geometry.Valid)
    (hl : LayoutPre input launch) {id : ThreadId} (hi : id.Valid launch.geometry) {slot : Nat} (hs : slot ≤ 4) :
    outputLoc input (context launch id) slot = ⟨.global,input.out+8*linear launch.geometry.block id+slot⟩ := by
  have hv := Dim3.volume_positive hg.2
  have hn := Dim3.linear_lt_volume hg.2 hi.2
  change linear launch.geometry.block id < launch.geometry.block.volume at hn
  have hi32 : linear launch.geometry.block id < 2^32 := by have := hl.count; omega
  have hout : input.out < 2^64 := by have := hl.extent; omega
  have hmul : linear launch.geometry.block id*8 < 2^64 := by omega
  have hsum : input.out+linear launch.geometry.block id*8 < 2^64 := by have := hl.extent; omega
  have hslot : input.out+linear launch.geometry.block id*8+slot < 2^64 := by have := hl.extent; omega
  have hraw : rawIndex (context launch id) = linear launch.geometry.block id := by
    rw [raw_index_is_linear_mod_u32]
    exact Nat.mod_eq_of_lt hi32
  simp only [outputLoc,address,hraw,w64,wrap,Nat.mod_eq_of_lt hout,Nat.mod_eq_of_lt hmul,
    Nat.mod_eq_of_lt hsum,Nat.mod_eq_of_lt hslot]
  simp only [Nat.mul_comm]

theorem layout_memory_event {mode input launch candidate actual kind}
    (hp : Params input launch.params) (hw : Shuffle.WellFormed (code mode) launch candidate)
    (hc : Shuffle.Complete candidate) (he : candidate.view.eventAt actual = some kind) :
    ∃ trace ∈ candidate.traces, ∃ slot : Fin 2, actual.thread = trace.id ∧ actual.serial = slot.val ∧
      (candidate.view.eventAt actual).bind Ptx.Event.Kind.footprint =
        some (outputLoc input (context launch trace.id) (4*slot.val),4) := by
  obtain ⟨trace,ht,hi,⟨hs,hk⟩ | ⟨hs,hk⟩⟩ := actual_memory_event_shape hp hw hc he
  · exact ⟨trace,ht,0,hi.symm,hs,by simp [he,hk,Ptx.Event.Kind.footprint]⟩
  · exact ⟨trace,ht,1,hi.symm,hs,by simp [he,hk,Ptx.Event.Kind.footprint]⟩

theorem unique_byte_writer {mode input launch candidate loc a b va vb}
    (hp : Params input launch.params) (hw : Shuffle.WellFormed (code mode) launch candidate)
    (hc : Shuffle.Complete candidate) (hl : LayoutPre input launch)
    (ha : candidate.view.writeByte a loc = some va) (hb : candidate.view.writeByte b loc = some vb) : a = b := by
  have hpa : candidate.view.Present a := Ptx.Event.accesses_present (Or.inr (by rw [ha]; rfl))
  have hpb : candidate.view.Present b := Ptx.Event.accesses_present (Or.inr (by rw [hb]; rfl))
  obtain ⟨ka,hka⟩ := Option.isSome_iff_exists.mp hpa
  obtain ⟨kb,hkb⟩ := Option.isSome_iff_exists.mp hpb
  obtain ⟨ta,hta,sa,hia,hsa,hfa⟩ := layout_memory_event hp hw hc hka
  obtain ⟨tb,htb,sb,hib,hsb,hfb⟩ := layout_memory_event hp hw hc hkb
  have hsa4 : 4*sa.val ≤ 4 := by have := sa.isLt; omega
  have hsb4 : 4*sb.val ≤ 4 := by have := sb.isLt; omega
  rw [output_location_layout hw.1 hl (hw.2.2.1 ta hta).1 hsa4] at hfa
  rw [output_location_layout hw.1 hl (hw.2.2.1 tb htb).1 hsb4] at hfb
  have hba := Ptx.Event.access_footprint_bounds (Or.inr (by rw [ha]; rfl)) hfa
  have hbb := Ptx.Event.access_footprint_bounds (Or.inr (by rw [hb]; rfl)) hfb
  have hindex : linear launch.geometry.block ta.id = linear launch.geometry.block tb.id := by
    have := sa.isLt; have := sb.isLt
    simp only at hba hbb
    omega
  have hslot : sa.val = sb.val := by
    have := sa.isLt; have := sb.isLt
    simp only at hba hbb
    omega
  have htid := valid_thread_index_unique hw.1 hl.grid (hw.2.2.1 ta hta).1 (hw.2.2.1 tb htb).1 hindex
  cases a; cases b
  simp only at hia hib hsa hsb
  simp only [hia,hib,hsa,hsb,htid,hslot]

end
end Ptx.Kernels.ShuffleProbe
