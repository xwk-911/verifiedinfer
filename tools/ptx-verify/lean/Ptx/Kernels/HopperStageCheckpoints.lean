import Ptx.Kernels.HopperStageData

/-! Normalized source checkpoints. Each segment is checked against the same
generated PTX data and fixed interpreter; no intermediate state is assumed.
The branch flag is derived from real launch coordinates. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def zeroLiteral : Scalar.F32Literal := ⟨0,by decide,by decide⟩
def zeroFloats : Scalar.FloatBindings := [("%d3",(.f32,zeroLiteral.value)),("%d2",(.f32,zeroLiteral.value)),
  ("%d1",(.f32,zeroLiteral.value)),("%d0",(.f32,zeroLiteral.value))]
def xWord (lane : Wgmma.Lane) : Nat := wrap 32 (tid lane).x
def yWord (lane : Wgmma.Lane) : Nat := wrap 32 (tid lane).y
def zWord (lane : Wgmma.Lane) : Nat := wrap 32 (tid lane).z
def sumWord (lane : Wgmma.Lane) : Nat :=
  wrap 32 (wrap 32 (wrap 32 (wrap 32 (xWord lane)+wrap 32 (yWord lane)))+wrap 32 (zWord lane))
def leaderWord (lane : Wgmma.Lane) : Nat := if decide (wrap 32 (sumWord lane) = wrap 32 0) then 1 else 0
def leader (lane : Wgmma.Lane) : Bool := decide (lane.val = 0)
def prefixRegs (lane : Wgmma.Lane) (flag : Nat) : Bindings := [
  ("%bd",wrap 64 68720001153),("%ad",wrap 64 68720001025),("%db",2064),("%da",16),("%bar",0),
  ("%leader",flag),("%sum",sumWord lane),("%z",zWord lane),("%y",yWord lane),("%x",xWord lane),
  ("%out",wrap 64 8192),("%mapb",wrap 64 4224),("%mapa",wrap 64 4096)]
def dirtyAt (pcs : List Nat) : List String := pcs.foldl (fun names pc =>
  (((Generated.hopper_gemm_stage.program[pc]?).map Wgmma.ordinaryNames).getD []++names).eraseDups) []
def at18 (lane : Wgmma.Lane) (flag : Nat) : Wgmma.State := {
  base := {scalar := {core := {thread := {pc := 18,regs := prefixRegs lane flag}},floats := zeroFloats}}
  ledger := {dirty := dirtyAt (List.range 18)}
}
theorem prefix_18 (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (lane : Wgmma.Lane) :
    Wgmma.run (ctx lane) (oracle a b lane) Generated.hopper_gemm_stage.program 18 {} =
      .ok (at18 lane (leaderWord lane),[]) := by rfl

theorem lane_sum_bounded (lane : Wgmma.Lane) : (tid lane).x+(tid lane).y+(tid lane).z < 14 := by
  have := lane.isLt
  dsimp [tid]
  omega
theorem coordinate_words (lane : Wgmma.Lane) :
    xWord lane = (tid lane).x ∧ yWord lane = (tid lane).y ∧ zWord lane = (tid lane).z := by
  have h := lane_sum_bounded lane
  dsimp [xWord,yWord,zWord,wrap]
  constructor
  · apply Nat.mod_eq_of_lt; omega
  · constructor <;> apply Nat.mod_eq_of_lt <;> omega
theorem sum_word_value (lane : Wgmma.Lane) : sumWord lane = (tid lane).x+(tid lane).y+(tid lane).z := by
  have h := lane_sum_bounded lane
  obtain ⟨hx,hy,hz⟩ := coordinate_words lane
  dsimp only [sumWord]
  rw [hx,hy,hz]
  have hx' : wrap 32 (tid lane).x = (tid lane).x := Nat.mod_eq_of_lt (by omega)
  have hy' : wrap 32 (tid lane).y = (tid lane).y := Nat.mod_eq_of_lt (by omega)
  have hz' : wrap 32 (tid lane).z = (tid lane).z := Nat.mod_eq_of_lt (by omega)
  have hs : wrap 32 ((tid lane).x+(tid lane).y) = (tid lane).x+(tid lane).y := Nat.mod_eq_of_lt (by omega)
  simp only [hx',hy',hz',hs]
  exact Nat.mod_eq_of_lt (by omega)
theorem coordinate_sum_zero (lane : Wgmma.Lane) : (tid lane).x+(tid lane).y+(tid lane).z = 0 ↔ lane.val = 0 := by
  change lane.val%4+(lane.val%32)/4+lane.val/32 = 0 ↔ lane.val = 0
  constructor
  · intro h
    have hz : lane.val/32 = 0 := by omega
    have hy : (lane.val%32)/4 = 0 := by omega
    have hx : lane.val%4 = 0 := by omega
    have hlt : lane.val < 32 := by omega
    rw [Nat.mod_eq_of_lt hlt] at hy
    omega
  · intro h; simp only [h,Nat.zero_mod,Nat.zero_div,Nat.add_zero]
theorem leader_word_value (lane : Wgmma.Lane) : leaderWord lane = if leader lane then 1 else 0 := by
  have hb : wrap 32 (sumWord lane) = sumWord lane := by
    apply Nat.mod_eq_of_lt
    rw [sum_word_value]
    have := lane_sum_bounded lane
    omega
  simp only [leaderWord,hb]
  change (if decide (sumWord lane = 0) then 1 else 0) = _
  rw [sum_word_value]
  simp only [coordinate_sum_zero,leader]
  rfl

end
end Ptx.Kernels.HopperStage
