import Ptx.ISA.LinearGeometry
import Mathlib.Data.List.Nodup

/-! Finite, duplicate-free enumeration of mathematical grid/block identities.
This supplies source coverage, not a GPU scheduling or allocation guarantee. -/
namespace Ptx.ISA

theorem Dim3.volume_positive {size : Dim3} (hp : size.Positive) : 0 < size.volume :=
  Nat.mul_pos (Nat.mul_pos hp.1 hp.2.1) hp.2.2

def Geometry.threadIdAt (geometry : Geometry) (index : Nat) : ThreadId :=
  ⟨geometry.grid.ofLinear (index/geometry.block.volume),geometry.block.ofLinear (index%geometry.block.volume)⟩
def ThreadId.launchIndex (id : ThreadId) (geometry : Geometry) : Nat :=
  id.cta.linear geometry.grid * geometry.block.volume + id.tid.linear geometry.block
def Geometry.threadIds (geometry : Geometry) : List ThreadId :=
  (List.range (geometry.grid.volume*geometry.block.volume)).map geometry.threadIdAt

theorem Geometry.threadIdAt_index (geometry : Geometry) (index : Nat) :
    (geometry.threadIdAt index).launchIndex geometry = index := by
  simp only [Geometry.threadIdAt,ThreadId.launchIndex,Dim3.linear_ofLinear]
  simpa only [Nat.mul_comm] using Nat.div_add_mod index geometry.block.volume

theorem Geometry.threadIdAt_injective (geometry : Geometry) : Function.Injective geometry.threadIdAt := by
  intro a b he
  have h := congrArg (fun id => id.launchIndex geometry) he
  simpa only [Geometry.threadIdAt_index] using h

theorem Geometry.threadIdAt_valid {geometry : Geometry} (hg : geometry.Valid) {index : Nat}
    (hi : index < geometry.grid.volume*geometry.block.volume) : (geometry.threadIdAt index).Valid geometry := by
  have hb := Dim3.volume_positive hg.2
  exact ⟨Dim3.ofLinear_within hg.1 ((Nat.div_lt_iff_lt_mul hb).2 hi),
    Dim3.ofLinear_within hg.2 (Nat.mod_lt _ hb)⟩

theorem ThreadId.launchIndex_lt {geometry : Geometry} (hg : geometry.Valid) {id : ThreadId} (hi : id.Valid geometry) :
    id.launchIndex geometry < geometry.grid.volume*geometry.block.volume := by
  have hc := Dim3.linear_lt_volume hg.1 hi.1
  have ht := Dim3.linear_lt_volume hg.2 hi.2
  have hm := Nat.mul_le_mul_right geometry.block.volume (Nat.succ_le_of_lt hc)
  dsimp [ThreadId.launchIndex]
  nlinarith

theorem Geometry.threadIdAt_launchIndex {geometry : Geometry} (hg : geometry.Valid) {id : ThreadId}
    (hi : id.Valid geometry) : geometry.threadIdAt (id.launchIndex geometry) = id := by
  have hb := Dim3.volume_positive hg.2
  have ht := Dim3.linear_lt_volume hg.2 hi.2
  have hdiv : id.launchIndex geometry/geometry.block.volume = id.cta.linear geometry.grid := by
    rw [ThreadId.launchIndex,Nat.mul_comm _ geometry.block.volume,Nat.mul_add_div hb,Nat.div_eq_of_lt ht,Nat.add_zero]
  have hmod : id.launchIndex geometry % geometry.block.volume = id.tid.linear geometry.block := by
    simp [ThreadId.launchIndex,Nat.add_mod,Nat.mod_eq_of_lt ht]
  cases id
  simp only [Geometry.threadIdAt,hdiv,hmod,Dim3.ofLinear_linear hg.1 hi.1,Dim3.ofLinear_linear hg.2 hi.2]

theorem Geometry.threadIds_nodup (geometry : Geometry) : geometry.threadIds.Nodup :=
  List.Nodup.map geometry.threadIdAt_injective List.nodup_range

theorem Geometry.threadIds_valid {geometry : Geometry} (hg : geometry.Valid) {id : ThreadId}
    (hi : id ∈ geometry.threadIds) : id.Valid geometry := by
  obtain ⟨index,hm,rfl⟩ := List.mem_map.mp hi
  exact Geometry.threadIdAt_valid hg (List.mem_range.mp hm)

theorem Geometry.threadIds_cover {geometry : Geometry} (hg : geometry.Valid) {id : ThreadId}
    (hi : id.Valid geometry) : id ∈ geometry.threadIds := by
  exact List.mem_map.mpr ⟨id.launchIndex geometry,List.mem_range.mpr (ThreadId.launchIndex_lt hg hi),
    Geometry.threadIdAt_launchIndex hg hi⟩

end Ptx.ISA
