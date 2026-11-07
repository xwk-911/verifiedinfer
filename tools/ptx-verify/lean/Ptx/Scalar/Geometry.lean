import Ptx.Scalar.Context
import Lean.Elab.Tactic.Omega

/-! Two-dimensional output ownership and coverage for scalar kernels. Geometry
is mathematical here; clients must separately prevent fixed-width arithmetic
overflow and discharge physical launch/allocation requirements. -/
namespace Ptx.Scalar
open Ptx.ISA

def row (block : Dim3) (id : ThreadId) : Nat := id.cta.y * block.y + id.tid.y
def col (block : Dim3) (id : ThreadId) : Nat := id.cta.x * block.x + id.tid.x

theorem tile_coordinate_injective {block a b x y : Nat} (hx : x < block) (hy : y < block)
    (he : a*block+x = b*block+y) : a = b ∧ x = y := by
  have hp : 0 < block := by omega
  have quotient : ∀ c t, t < block → (c*block+t)/block = c := by
    intro c t ht
    rw [Nat.mul_comm c block,Nat.mul_add_div hp,Nat.div_eq_of_lt ht,Nat.add_zero]
  have hdiv := congrArg (fun n => n/block) he
  rw [quotient a x hx,quotient b y hy] at hdiv
  subst b
  exact ⟨rfl,by omega⟩

theorem output_coordinates_injective {g : Geometry} (hg : g.grid.z = 1) (hb : g.block.z = 1)
    {a b : ThreadId} (ha : a.Valid g) (hv : b.Valid g)
    (hr : row g.block a = row g.block b) (hc : col g.block a = col g.block b) : a = b := by
  have hx := tile_coordinate_injective ha.2.1 hv.2.1 hc
  have hy := tile_coordinate_injective ha.2.2.1 hv.2.2.1 hr
  rcases a with ⟨⟨ax,ay,az⟩,⟨tx,ty,tz⟩⟩
  rcases b with ⟨⟨bx,byc,bz⟩,⟨ux,uy,uz⟩⟩
  simp only [ThreadId.Valid,Dim3.Within,hg,hb] at ha hv
  simp only at hx hy
  obtain ⟨rfl,rfl⟩ := hx
  obtain ⟨rfl,rfl⟩ := hy
  have hz : az = 0 ∧ bz = 0 ∧ tz = 0 ∧ uz = 0 := by omega
  rcases hz with ⟨rfl,rfl,rfl,rfl⟩
  rfl

theorem output_coordinate_covered {g : Geometry} (hv : g.Valid) {r c : Nat}
    (hr : r < g.grid.y*g.block.y) (hc : c < g.grid.x*g.block.x) :
    ∃ id, id.Valid g ∧ row g.block id = r ∧ col g.block id = c := by
  let id : ThreadId := ⟨⟨c/g.block.x,r/g.block.y,0⟩,⟨c%g.block.x,r%g.block.y,0⟩⟩
  refine ⟨id,?_,?_,?_⟩
  · exact ⟨⟨(Nat.div_lt_iff_lt_mul hv.2.1).mpr hc,
      (Nat.div_lt_iff_lt_mul hv.2.2.1).mpr hr,hv.1.2.2⟩,
      ⟨Nat.mod_lt _ hv.2.1,Nat.mod_lt _ hv.2.2.1,hv.2.2.2⟩⟩
  · simpa only [row,id,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div r g.block.y
  · simpa only [col,id,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div c g.block.x

theorem matrix_index_injective {r s c d n : Nat} (hc : c < n) (hd : d < n)
    (he : r*n+c = s*n+d) : r = s ∧ c = d := tile_coordinate_injective hc hd he

end Ptx.Scalar
