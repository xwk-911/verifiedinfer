import Ptx.Kernels.MoeCombineThread
import Ptx.Scalar.Regions
import Mathlib.Tactic.Ring

/-! Full R/H/Y byte footprints, alignment and separation for the gather.
Only selected H values require initialization. These bounds do not establish
physical allocation/runtime or full ISA correspondence. -/
namespace Ptx.MoeCombineEvent
open Ptx.ISA Ptx.Scalar Ptx.MoeCombine
noncomputable section

structure Config where
  input : Inputs
  geometry : Geometry
  valid : geometry.Valid
  gridZ : geometry.grid.z = 1
  blockZ : geometry.block.z = 1
  gridX32 : geometry.grid.x < 2^32
  gridY32 : geometry.grid.y < 2^32
  blockX32 : geometry.block.x < 2^32
  blockY32 : geometry.block.y < 2^32
  extentX32 : geometry.grid.x*geometry.block.x ≤ 2^32
  extentY32 : geometry.grid.y*geometry.block.y ≤ 2^32
  coversRows : input.m ≤ geometry.grid.y*geometry.block.y
  coversCols : input.n ≤ geometry.grid.x*geometry.block.x
  rEnd : 0 < input.n → input.r+4*input.m ≤ 2^64
  hEnd : input.h+4*((2*input.m)*input.n) ≤ 2^64
  yEnd : input.y+4*(input.m*input.n) ≤ 2^64
  rAligned : 0 < input.m → 0 < input.n → input.r % 4 = 0
  hAligned : 0 < input.m → 0 < input.n → input.h % 4 = 0
  yAligned : 0 < input.m → 0 < input.n → input.y % 4 = 0
  separateR : WordsDisjoint input.r input.m input.y (input.m*input.n)
  separateH : WordsDisjoint input.h ((2*input.m)*input.n) input.y (input.m*input.n)

def context (cfg : Config) (params : Bindings) (id : ThreadId) : Scalar.Context :=
  {id := id,params := params,block := cfg.geometry.block}
def Active (cfg : Config) (id : ThreadId) : Prop :=
  row cfg.geometry.block id < cfg.input.m ∧ col cfg.geometry.block id < cfg.input.n
def rLoc (cfg : Config) (r : Nat) : Location := ⟨.global,cfg.input.r+4*r⟩
def hLoc (cfg : Config) (e r c : Nat) : Location := ⟨.global,cfg.input.h+4*((e*cfg.input.m+r)*cfg.input.n+c)⟩
def yLoc (cfg : Config) (r c : Nat) : Location := ⟨.global,cfg.input.y+4*(r*cfg.input.n+c)⟩

theorem index_bounds (cfg : Config) {id : ThreadId} (hv : id.Valid cfg.geometry) (params : Bindings) :
    IndexBounds (context cfg params id) :=
  Indexing.bounds_of_launch cfg.gridX32 cfg.gridY32 cfg.blockX32 cfg.blockY32 cfg.extentX32 cfg.extentY32 hv params
theorem h_index_bound (cfg : Config) {e r c} (he : e < 2) (hr : r < cfg.input.m) (hc : c < cfg.input.n) :
    (e*cfg.input.m+r)*cfg.input.n+c < (2*cfg.input.m)*cfg.input.n := matrix_index_lt (matrix_index_lt he hr) hc
theorem y_index_bound (cfg : Config) {r c} (hr : r < cfg.input.m) (hc : c < cfg.input.n) :
    r*cfg.input.n+c < cfg.input.m*cfg.input.n := matrix_index_lt hr hc

theorem h_address (i : Inputs) (e r c : Nat) :
    hBase i e+4*(r*i.n+c) = i.h+4*((e*i.m+r)*i.n+c) := by unfold hBase; ring

theorem route_pointer_bound (cfg : Config) {id : ThreadId} (ha : Active cfg id) :
    cfg.input.r+4*row cfg.geometry.block id < 2^64 := by
  have hend := cfg.rEnd (by have := ha.2; omega)
  have hr := ha.1
  omega
theorem address_bounds (cfg : Config) (params : Bindings) {id : ThreadId} (ha : Active cfg id) {e : Nat} (he : e < 2) :
    AddressBounds cfg.input (context cfg params id) e := by
  constructor
  · change hBase cfg.input e+4*(row cfg.geometry.block id*cfg.input.n+col cfg.geometry.block id) < 2^64
    rw [h_address]
    have hi := h_index_bound cfg he ha.1 ha.2
    have hend := cfg.hEnd
    omega
  · have hi := y_index_bound cfg ha.1 ha.2
    have hend := cfg.yEnd
    change cfg.input.y+4*(row cfg.geometry.block id*cfg.input.n+col cfg.geometry.block id) < 2^64
    omega

theorem r_footprint (cfg : Config) {r offset} (hr : r < cfg.input.m) (hn : 0 < cfg.input.n) (ho : offset < 4) :
    ((rLoc cfg r).add offset).address < 2^64 := by
  have he := cfg.rEnd hn
  simp only [rLoc,Location.add]
  omega
theorem h_footprint (cfg : Config) {e r c offset} (he : e < 2) (hr : r < cfg.input.m) (hc : c < cfg.input.n)
    (ho : offset < 4) : ((hLoc cfg e r c).add offset).address < 2^64 := by
  have hi := h_index_bound cfg he hr hc
  have hend := cfg.hEnd
  simp only [hLoc,Location.add]
  omega

theorem y_footprint (cfg : Config) {r c offset} (hr : r < cfg.input.m) (hc : c < cfg.input.n)
    (ho : offset < 4) : ((yLoc cfg r c).add offset).address < 2^64 := by
  have hi := y_index_bound cfg hr hc
  have hend := cfg.yEnd
  simp only [yLoc,Location.add]
  omega
theorem r_aligned (cfg : Config) {r} (hr : r < cfg.input.m) (hn : 0 < cfg.input.n) :
    (rLoc cfg r).address % 4 = 0 := by simp [rLoc,Nat.add_mod,cfg.rAligned (by omega) hn]
theorem h_aligned (cfg : Config) {e r c} (hr : r < cfg.input.m) (hc : c < cfg.input.n) :
    (hLoc cfg e r c).address % 4 = 0 := by simp [hLoc,Nat.add_mod,cfg.hAligned (by omega) (by omega)]
theorem y_aligned (cfg : Config) {r c} (hr : r < cfg.input.m) (hc : c < cfg.input.n) :
    (yLoc cfg r c).address % 4 = 0 := by simp [yLoc,Nat.add_mod,cfg.yAligned (by omega) (by omega)]

def Initialized (cfg : Config) (gates values : Moe.Matrix) (initial : Scalar.ByteMap) : Prop :=
  (∀ r, r < cfg.input.m → 0 < cfg.input.n → RepresentsU32 initial (rLoc cfg r) (Moe.selected gates r)) ∧
  (∀ r c, r < cfg.input.m → c < cfg.input.n →
    RepresentsReal .f32 initial (hLoc cfg (Moe.selected gates r) r c) (values r c))
def Pre (cfg : Config) (gates values : Moe.Matrix) (launch : Scalar.Launch) : Prop :=
  launch.geometry = cfg.geometry ∧ Params cfg.input launch.params ∧ Initialized cfg gates values launch.initial
def Post (cfg : Config) (values : Moe.Matrix) (memory : Scalar.ByteMap) : Prop :=
  ∀ r c, r < cfg.input.m → c < cfg.input.n → RepresentsReal .f32 memory (yLoc cfg r c) (values r c)

end
end Ptx.MoeCombineEvent
