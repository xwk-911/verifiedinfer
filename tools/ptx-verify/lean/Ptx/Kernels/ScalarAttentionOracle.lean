import Ptx.Kernels.ScalarAttentionOuter

/-! A concrete typed reply function for constructive LOCAL source execution.
Its values still need to be justified by initial memory in a global witness. -/
namespace Ptx.ScalarAttentionOracle
open Ptx.ISA Ptx.Scalar
noncomputable section

def answers (q key value : Attention.Matrix) (row col dim : Nat) (scale : ℝ) : Scalar.Oracle := fun query =>
  .real .f32 (if query = 0 then scale else
    let queryOffset := query-1
    let item := queryOffset/(2*dim+1)
    let slot := queryOffset%(2*dim+1)
    if slot = 2*dim then value item col else
      if slot%2 = 0 then q row (slot/2) else key item (slot/2))

theorem scale_reply (q key value : Attention.Matrix) (row col dim : Nat) (scale : ℝ) :
    answers q key value row col dim scale 0 = .real .f32 scale := rfl

theorem slot (dim item offset : Nat) (hoff : offset < 2*dim+1) :
    (1+(2*dim+1)*item+offset-1)/(2*dim+1) = item ∧
      (1+(2*dim+1)*item+offset-1)%(2*dim+1) = offset := by
  have he : 1+(2*dim+1)*item+offset-1 = (2*dim+1)*item+offset := by omega
  rw [he]
  constructor
  · rw [Nat.mul_add_div (by omega : 0 < 2*dim+1),Nat.div_eq_of_lt hoff,Nat.add_zero]
  · simp [Nat.add_mod,Nat.mod_eq_of_lt hoff]

theorem q_reply (q key value : Attention.Matrix) (row col dim item k : Nat) (scale : ℝ) (hk : k < dim) :
    answers q key value row col dim scale (1+(2*dim+1)*item+2*k) = .real .f32 (q row k) := by
  obtain ⟨hi,hs⟩ := slot dim item (2*k) (by omega)
  have hn : 1+(2*dim+1)*item+2*k ≠ 0 := by omega
  have hd : 2*k ≠ 2*dim := by omega
  simp [answers,hn,hi,hs,hd,Nat.mul_div_right]

theorem key_reply (q key value : Attention.Matrix) (row col dim item k : Nat) (scale : ℝ) (hk : k < dim) :
    answers q key value row col dim scale (1+(2*dim+1)*item+2*k+1) = .real .f32 (key item k) := by
  have he : 1+(2*dim+1)*item+2*k+1 = 1+(2*dim+1)*item+(2*k+1) := by omega
  rw [he]
  obtain ⟨hi,hs⟩ := slot dim item (2*k+1) (by omega)
  have hn : 1+(2*dim+1)*item+(2*k+1) ≠ 0 := by omega
  have hd : 2*k+1 ≠ 2*dim := by omega
  have hk2 : (2*k+1)/2 = k := by omega
  have hm2 : (2*k+1)%2 = 1 := by omega
  simp only [answers,hn,ite_false,hi,hs]
  simp [hd,hk2,hm2]

theorem value_reply (q key value : Attention.Matrix) (row col dim item : Nat) (scale : ℝ) :
    answers q key value row col dim scale (1+(2*dim+1)*item+2*dim) = .real .f32 (value item col) := by
  obtain ⟨hi,hs⟩ := slot dim item (2*dim) (by omega)
  have hn : 1+(2*dim+1)*item+2*dim ≠ 0 := by omega
  simp [answers,hn,hi,hs]

end
end Ptx.ScalarAttentionOracle
