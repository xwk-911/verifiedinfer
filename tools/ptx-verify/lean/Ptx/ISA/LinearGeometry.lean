import Ptx.ISA.Launch
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Mathematical three-dimensional linearization, inversion and coverage.
No hardware launch limits, fixed-width arithmetic or allocation are asserted. -/
namespace Ptx.ISA

theorem Dim3.linear_lt_volume {index size : Dim3} (_hp : size.Positive) (hi : index.Within size) :
    index.linear size < size.volume := by
  have hyz : index.y + size.y*index.z < size.y*size.z := by
    have hmul := Nat.mul_le_mul_left size.y (Nat.succ_le_of_lt hi.2.2)
    nlinarith [hi.2.1]
  have hmul := Nat.mul_le_mul_left size.x (Nat.succ_le_of_lt hyz)
  dsimp [Dim3.linear,Dim3.volume]
  nlinarith [hi.1]

def Dim3.ofLinear (size : Dim3) (index : Nat) : Dim3 :=
  ⟨index % size.x,(index/size.x) % size.y,(index/size.x)/size.y⟩

theorem Dim3.ofLinear_within {size : Dim3} (hp : size.Positive) {index : Nat} (hi : index < size.volume) :
    (size.ofLinear index).Within size := by
  refine ⟨Nat.mod_lt _ hp.1,Nat.mod_lt _ hp.2.1,?_⟩
  have hx : index/size.x < size.y*size.z := (Nat.div_lt_iff_lt_mul hp.1).2 (by
    simpa only [Dim3.volume,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hi)
  exact (Nat.div_lt_iff_lt_mul hp.2.1).2 (by simpa only [Nat.mul_comm] using hx)

theorem Dim3.linear_ofLinear (size : Dim3) (index : Nat) : (size.ofLinear index).linear size = index := by
  have hy := Nat.mod_add_div (index/size.x) size.y
  have hx := Nat.mod_add_div index size.x
  simpa only [Dim3.ofLinear,Dim3.linear,hy] using hx

theorem Dim3.ofLinear_linear {size index : Dim3} (hp : size.Positive) (hi : index.Within size) :
    size.ofLinear (index.linear size) = index := by
  have hx : index.linear size % size.x = index.x := by
    simp [Dim3.linear,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt hi.1]
  have hdiv : index.linear size/size.x = index.y+size.y*index.z := by
    dsimp [Dim3.linear]
    rw [Nat.add_comm index.x,Nat.mul_add_div hp.1,Nat.div_eq_of_lt hi.1,Nat.add_zero]
  have hy : (index.y+size.y*index.z) % size.y = index.y := by
    simp [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt hi.2.1]
  have hz : (index.y+size.y*index.z)/size.y = index.z := by
    rw [Nat.add_comm index.y,Nat.mul_add_div hp.2.1,Nat.div_eq_of_lt hi.2.1,Nat.add_zero]
  cases index
  simp only [Dim3.ofLinear,hx,hdiv,hy,hz]

theorem Dim3.linear_injective {size a b : Dim3} (hp : size.Positive) (ha : a.Within size) (hb : b.Within size)
    (he : a.linear size = b.linear size) : a = b := by
  have h := congrArg size.ofLinear he
  simpa only [Dim3.ofLinear_linear hp ha,Dim3.ofLinear_linear hp hb] using h

end Ptx.ISA
