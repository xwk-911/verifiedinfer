import Ptx.Kernels.MoeRouteThread
import Ptx.Scalar.Regions

/-! One-dimensional route launch and byte-layout preconditions. Geometry,
full word bounds, separation and represented initial gates are explicit.
For M=0 no data initialization, alignment or separation is required. -/
namespace Ptx.MoeRouteEvent
open Ptx.ISA Ptx.Scalar Ptx.MoeRouteThread
noncomputable section

structure Config where
  input : Inputs
  geometry : Geometry
  valid : geometry.Valid
  gridY : geometry.grid.y = 1
  gridZ : geometry.grid.z = 1
  blockY : geometry.block.y = 1
  blockZ : geometry.block.z = 1
  gridX32 : geometry.grid.x < 2^32
  blockX32 : geometry.block.x < 2^32
  extent32 : geometry.grid.x*geometry.block.x ≤ 2^32
  covers : input.m ≤ geometry.grid.x*geometry.block.x
  gEnd : input.g+4*(2*input.m) ≤ 2^64
  rEnd : input.r+4*input.m ≤ 2^64
  gAligned : 0 < input.m → input.g % 4 = 0
  rAligned : 0 < input.m → input.r % 4 = 0
  separate : WordsDisjoint input.g (2*input.m) input.r input.m

def context (cfg : Config) (params : Bindings) (id : ThreadId) : Scalar.Context :=
  {id := id,params := params,block := cfg.geometry.block}
def index (cfg : Config) (id : ThreadId) : Nat := col cfg.geometry.block id
def gLoc (cfg : Config) (row gate : Nat) : Location := ⟨.global,cfg.input.g+4*(2*row+gate)⟩
def rLoc (cfg : Config) (row : Nat) : Location := ⟨.global,cfg.input.r+4*row⟩
def Active (cfg : Config) (id : ThreadId) : Prop := index cfg id < cfg.input.m

@[simp] theorem g_zero (cfg : Config) (row : Nat) : gLoc cfg row 0 = ⟨.global,cfg.input.g+8*row⟩ := by
  unfold gLoc
  congr 1 <;> omega
@[simp] theorem g_one (cfg : Config) (row : Nat) : gLoc cfg row 1 = ⟨.global,cfg.input.g+8*row+4⟩ := by
  unfold gLoc
  congr 1 <;> omega

theorem index_bounds (cfg : Config) {id : ThreadId} (hv : id.Valid cfg.geometry) (params : Bindings) :
    Bounds (context cfg params id) := by
  have hi := Indexing.col_below_grid hv
  constructor
  · have h := hv.1.1; have hb := cfg.gridX32; change id.cta.x < 2^32; omega
  · exact cfg.blockX32
  · have h := hv.2.1; have hb := cfg.blockX32; change id.tid.x < 2^32; omega
  · exact lt_of_lt_of_le hi cfg.extent32

theorem gate_index_bound (cfg : Config) {row gate : Nat} (hr : row < cfg.input.m) (hg : gate < 2) :
    2*row+gate < 2*cfg.input.m := by omega
theorem gate_end (cfg : Config) {row : Nat} (hr : row < cfg.input.m) :
    cfg.input.g+8*row+8 ≤ 2^64 := by have h := cfg.gEnd; omega
theorem route_end (cfg : Config) {row : Nat} (hr : row < cfg.input.m) :
    cfg.input.r+4*row+4 ≤ 2^64 := by have h := cfg.rEnd; omega

theorem gate_footprint (cfg : Config) {row gate offset : Nat}
    (hr : row < cfg.input.m) (hg : gate < 2) (ho : offset < 4) :
    ((gLoc cfg row gate).add offset).address < 2^64 := by
  have hi := gate_index_bound cfg hr hg
  have he := cfg.gEnd
  simp only [gLoc,Location.add]
  omega
theorem route_footprint (cfg : Config) {row offset : Nat} (hr : row < cfg.input.m) (ho : offset < 4) :
    ((rLoc cfg row).add offset).address < 2^64 := by
  have he := cfg.rEnd
  simp only [rLoc,Location.add]
  omega
theorem gate_aligned (cfg : Config) {row : Nat} (hr : row < cfg.input.m) (gate : Nat) :
    (gLoc cfg row gate).address % 4 = 0 := by
  simp [gLoc,Nat.add_mod,cfg.gAligned (by omega)]
theorem route_aligned (cfg : Config) {row : Nat} (hr : row < cfg.input.m) :
    (rLoc cfg row).address % 4 = 0 := by
  simp [rLoc,Nat.add_mod,cfg.rAligned (by omega)]

theorem index_injective (cfg : Config) {a b : ThreadId} (ha : a.Valid cfg.geometry) (hb : b.Valid cfg.geometry)
    (he : index cfg a = index cfg b) : a = b := by
  have ay : a.cta.y = 0 := by have := ha.1.2.1; rw [cfg.gridY] at this; omega
  have byc : b.cta.y = 0 := by have := hb.1.2.1; rw [cfg.gridY] at this; omega
  have ty : a.tid.y = 0 := by have := ha.2.2.1; rw [cfg.blockY] at this; omega
  have uy : b.tid.y = 0 := by have := hb.2.2.1; rw [cfg.blockY] at this; omega
  exact output_coordinates_injective cfg.gridZ cfg.blockZ ha hb (by simp [row,ay,byc,ty,uy]) he

theorem index_covered (cfg : Config) {r : Nat} (hr : r < cfg.input.m) :
    ∃ id, id.Valid cfg.geometry ∧ index cfg id = r := by
  obtain ⟨id,hv,_,hc⟩ := output_coordinate_covered cfg.valid
    (r := 0) (c := r) (by simp [cfg.gridY,cfg.blockY]) (by have := cfg.covers; omega)
  exact ⟨id,hv,hc⟩

def Initialized (cfg : Config) (gates : Moe.Matrix) (initial : Scalar.ByteMap) : Prop :=
  ∀ row gate, row < cfg.input.m → gate < 2 → RepresentsReal .f32 initial (gLoc cfg row gate) (gates row gate)
def Pre (cfg : Config) (gates : Moe.Matrix) (launch : Scalar.Launch) : Prop :=
  launch.geometry = cfg.geometry ∧ Params cfg.input launch.params ∧ Initialized cfg gates launch.initial

end
end Ptx.MoeRouteEvent
