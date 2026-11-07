import Ptx.Kernels.ShuffleProbeValues
import Ptx.ISA.LinearGeometry

/-! Static, finite launch closure discharges source shuffle definedness.
The precondition mentions input words and linear launch indices, never oracle
answers, desired results or candidate Defined. It includes partial warps when
every launched caller and selected source belongs to the named active lanes. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

def LaunchClosed (mode : Mode) (input : Inputs) (block : Dim3) : Prop :=
  ∀ index : Fin block.volume,
    member (w32 input.mask) (BitVec.ofNat 5 index.val) = true ∧
    32*(index.val/32) + (select mode (BitVec.ofNat 5 index.val) (w32 input.b) (w32 input.c)).source.toNat < block.volume
instance (mode input block) : Decidable (LaunchClosed mode input block) := by
  unfold LaunchClosed
  infer_instance

def SafePre (mode : Mode) (input : Inputs) (launch : Scalar.Launch) : Prop :=
  launch.geometry.Valid ∧ Params input launch.params ∧ LaunchClosed mode input launch.geometry.block

theorem selected_thread_exists {mode : Mode} {input : Inputs} {launch : Scalar.Launch} {origin : ThreadId}
    (hg : launch.geometry.Valid)
    (hl : LaunchClosed mode input launch.geometry.block) (hv : origin.Valid launch.geometry) :
    ∃ peer, peer.Valid launch.geometry ∧ SameWarp launch.geometry.block origin peer ∧
      lane launch.geometry.block peer = (select mode (lane launch.geometry.block origin) (w32 input.b) (w32 input.c)).source ∧
      member (w32 input.mask) (lane launch.geometry.block peer) = true := by
  have hindex : linear launch.geometry.block origin < launch.geometry.block.volume := Dim3.linear_lt_volume hg.2 hv.2
  let index : Fin launch.geometry.block.volume := ⟨linear launch.geometry.block origin,hindex⟩
  let selected := (select mode (lane launch.geometry.block origin) (w32 input.b) (w32 input.c)).source
  let target := 32*(linear launch.geometry.block origin/32)+selected.toNat
  have ht : target < launch.geometry.block.volume := (hl index).2
  let peer : ThreadId := ⟨origin.cta,launch.geometry.block.ofLinear target⟩
  have hlin : linear launch.geometry.block peer = target := Dim3.linear_ofLinear _ _
  have hwarp : linear launch.geometry.block peer/32 = linear launch.geometry.block origin/32 := by
    rw [hlin]
    dsimp [target]
    rw [Nat.mul_add_div (by decide : 0 < 32),Nat.div_eq_of_lt selected.isLt,Nat.add_zero]
  have hlane : lane launch.geometry.block peer = selected := by
    apply BitVec.eq_of_toNat_eq
    simp only [lane,BitVec.toNat_ofNat,hlin]
    dsimp [target]
    have := selected.isLt
    omega
  refine ⟨peer,⟨hv.1,Dim3.ofLinear_within hg.2 ht⟩,⟨rfl,hwarp.symm⟩,hlane,?_⟩
  simpa only [lane,hlin] using (hl ⟨target,ht⟩).1

theorem every_member_arrived {mode input launch candidate trace} (hp : Params input launch.params)
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (ht : trace ∈ candidate.traces) : Arrived candidate trace.id (groupKey mode input) 0 :=
  ⟨0,record mode input (context launch trace.id) (trace.oracle.shuffle 0).1 (trace.oracle.shuffle 0).2,
    shuffle_member_lookup hp hw hc ht,rfl,rfl⟩

theorem completed_member_matched {mode input launch candidate trace} (hp : Params input launch.params)
    (hl : LaunchClosed mode input launch.geometry.block) (hw : Shuffle.WellFormed (code mode) launch candidate)
    (hc : Shuffle.Complete candidate) (ht : trace ∈ candidate.traces) :
    Matched launch.geometry.block candidate ⟨trace.id,0⟩
      (record mode input (context launch trace.id) (trace.oracle.shuffle 0).1 (trace.oracle.shuffle 0).2) := by
  have hindex : linear launch.geometry.block trace.id < launch.geometry.block.volume :=
    Dim3.linear_lt_volume hw.1.2 (hw.2.2.1 trace ht).1.2
  refine ⟨(hl ⟨linear launch.geometry.block trace.id,hindex⟩).1,?_⟩
  intro other hm _ _
  exact Or.inl (every_member_arrived hp hw hc hm)

theorem all_completed_defined {mode input launch candidate} (hp : Params input launch.params)
    (hl : LaunchClosed mode input launch.geometry.block) (hw : Shuffle.WellFormed (code mode) launch candidate)
    (hc : Shuffle.Complete candidate) : Defined launch.geometry.block candidate := by
  intro origin result he
  obtain ⟨trace,ht,hi,hn,hr⟩ := actual_shuffle_shape hp hw hc he
  rcases origin with ⟨thread,serial⟩
  dsimp only at hi hn
  subst thread; subst serial; subst result
  obtain ⟨peerId,hv,hs,hsel,hmember⟩ := selected_thread_exists hw.1 hl (hw.2.2.1 trace ht).1
  obtain ⟨peer,hm,hid⟩ := hw.2.2.2 peerId hv
  refine ⟨completed_member_matched hp hl hw hc ht,⟨peer.id,0⟩,
    record mode input (context launch peer.id) (peer.oracle.shuffle 0).1 (peer.oracle.shuffle 0).2,
    shuffle_member_lookup hp hw hc hm,?_,?_,?_,rfl,rfl⟩
  · simpa only [hid] using hs
  · simpa only [hid,record,groupKey] using hsel
  · simpa only [hid,record,groupKey] using hmember

theorem exported_source_safe (mode : Mode) (input : Inputs) : Shuffle.Safe (code mode) (SafePre mode input) := by
  intro launch candidate rf co hp hw hc _ _ _
  exact all_completed_defined hp.2.1 hp.2.2 hw hc

end
end Ptx.Kernels.ShuffleProbe
