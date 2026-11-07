import Ptx.Generated.ScalarMatmul
import Ptx.Scalar.Geometry
import Ptx.Scalar.Memory

/-! Independent row-major matrix specification. The recurrence keeps the source
FMA's multiplication/addition order. Geometry facts do not prove the fixed-width
index instructions cannot wrap; that remains a kernel precondition/proof duty.
-/
namespace Ptx.ScalarMatmul
open Ptx.ISA Ptx.Scalar
noncomputable section

abbrev code := Generated.scalar_matmul.program
abbrev Matrix := Nat → Nat → ℝ

def prefixProduct (a b : Matrix) (r c : Nat) : Nat → ℝ
  | 0 => 0
  | k+1 => a r k * b k c + prefixProduct a b r c k

def Post (a b : Matrix) (m n k base : Nat) (memory : Scalar.ByteMap) : Prop :=
  ∀ r c, r < m → c < n →
    RepresentsReal .f32 memory ⟨.global,base+4*(r*n+c)⟩ (prefixProduct a b r c k)

theorem zero_inner_dimension (a b : Matrix) (r c : Nat) : prefixProduct a b r c 0 = 0 := rfl

theorem accumulation_step (a b : Matrix) (r c k : Nat) (acc : ℝ)
    (hi : acc = prefixProduct a b r c k) :
    a r k * b k c + acc = prefixProduct a b r c (k+1) := by rw [hi]; rfl

theorem output_index_unique {g : Geometry} (hz : g.grid.z = 1) (hb : g.block.z = 1)
    {a b : ThreadId} (ha : a.Valid g) (hv : b.Valid g) {n : Nat}
    (hc : col g.block a < n) (hd : col g.block b < n)
    (he : row g.block a*n+col g.block a = row g.block b*n+col g.block b) : a = b := by
  have h := matrix_index_injective hc hd he
  exact output_coordinates_injective hz hb ha hv h.1 h.2

theorem output_covered {g : Geometry} (hv : g.Valid) {m n r c : Nat}
    (hm : m ≤ g.grid.y*g.block.y) (hn : n ≤ g.grid.x*g.block.x) (hr : r < m) (hc : c < n) :
    ∃ id, id.Valid g ∧ row g.block id = r ∧ col g.block id = c :=
  output_coordinate_covered hv (by omega) (by omega)

end
end Ptx.ScalarMatmul
