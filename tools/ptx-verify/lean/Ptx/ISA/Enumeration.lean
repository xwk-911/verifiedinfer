import Ptx.ISA.Launch
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range

/-! Finite, duplicate-free enumeration of arbitrary launch geometries. No
hardware launch limit or progress property is assumed by this enumeration. -/
namespace Ptx.ISA

def Dim3.indices (size : Dim3) : Finset Dim3 :=
  (((Finset.range size.x).product (Finset.range size.y)).product (Finset.range size.z)).image
    (fun p => ⟨p.1.1,p.1.2,p.2⟩)

@[simp] theorem Dim3.mem_indices {size index : Dim3} : index ∈ size.indices ↔ index.Within size := by
  rcases index with ⟨x,y,z⟩
  simp [Dim3.indices,Dim3.Within,Finset.mem_image,Prod.exists,Dim3.mk.injEq,and_assoc]

noncomputable def Geometry.threads (g : Geometry) : List ThreadId :=
  ((g.grid.indices.product g.block.indices).image (fun p => ThreadId.mk p.1 p.2)).toList

@[simp] theorem Geometry.mem_threads {g : Geometry} {id : ThreadId} :
    id ∈ g.threads ↔ id.Valid g := by
  rcases id with ⟨cta,tid⟩
  simp [Geometry.threads,Finset.mem_image,Prod.exists,ThreadId.Valid,ThreadId.mk.injEq]

theorem Geometry.threads_nodup (g : Geometry) : g.threads.Nodup := Finset.nodup_toList _

end Ptx.ISA
