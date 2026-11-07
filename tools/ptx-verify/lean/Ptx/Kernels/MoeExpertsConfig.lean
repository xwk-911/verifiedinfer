import Ptx.Kernels.MoeExpertsThread
import Ptx.Scalar.Regions
import Mathlib.Tactic.Ring

/-! Full live-byte layout for the two expert planes. Dead X/W regions at K=0
and all input regions when rows/columns are empty need no unused-read premises.
These bounds do not prove physical allocation/runtime or full ISA compliance. -/
namespace Ptx.MoeExpertsEvent
open Ptx.ISA Ptx.Scalar Ptx.MoeExperts Ptx.MoeExpertsLoop
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
  xEnd : 0 < input.n → input.x+4*(input.m*input.k) ≤ 2^64
  wEnd : 0 < input.m → input.w+4*((2*input.k)*input.n) ≤ 2^64
  hEnd : input.h+4*((2*input.m)*input.n) ≤ 2^64
  rAligned : 0 < input.m → 0 < input.n → input.r % 4 = 0
  xAligned : 0 < input.m → 0 < input.n → 0 < input.k → input.x % 4 = 0
  wAligned : 0 < input.m → 0 < input.n → 0 < input.k → input.w % 4 = 0
  hAligned : 0 < input.m → 0 < input.n → input.h % 4 = 0
  separateR : WordsDisjoint input.r input.m input.h ((2*input.m)*input.n)
  separateX : WordsDisjoint input.x (input.m*input.k) input.h ((2*input.m)*input.n)
  separateW : WordsDisjoint input.w ((2*input.k)*input.n) input.h ((2*input.m)*input.n)

def context (cfg : Config) (params : Bindings) (id : ThreadId) : Scalar.Context :=
  {id := id,params := params,block := cfg.geometry.block}
def Active (cfg : Config) (id : ThreadId) : Prop :=
  row cfg.geometry.block id < cfg.input.m ∧ col cfg.geometry.block id < cfg.input.n
def rLoc (cfg : Config) (r : Nat) : Location := ⟨.global,cfg.input.r+4*r⟩
def xLoc (cfg : Config) (r k : Nat) : Location := ⟨.global,cfg.input.x+4*(r*cfg.input.k+k)⟩
def wLoc (cfg : Config) (e k c : Nat) : Location := ⟨.global,cfg.input.w+4*((e*cfg.input.k+k)*cfg.input.n+c)⟩
def hLoc (cfg : Config) (e r c : Nat) : Location := ⟨.global,cfg.input.h+4*((e*cfg.input.m+r)*cfg.input.n+c)⟩

theorem index_bounds (cfg : Config) {id : ThreadId} (hv : id.Valid cfg.geometry) (params : Bindings) :
    IndexBounds (context cfg params id) :=
  Indexing.bounds_of_launch cfg.gridX32 cfg.gridY32 cfg.blockX32 cfg.blockY32 cfg.extentX32 cfg.extentY32 hv params
theorem x_index_bound (cfg : Config) {r k} (hr : r < cfg.input.m) (hk : k < cfg.input.k) :
    r*cfg.input.k+k < cfg.input.m*cfg.input.k := matrix_index_lt hr hk
theorem w_index_bound (cfg : Config) {e k c} (he : e < 2) (hk : k < cfg.input.k) (hc : c < cfg.input.n) :
    (e*cfg.input.k+k)*cfg.input.n+c < (2*cfg.input.k)*cfg.input.n := matrix_index_lt (matrix_index_lt he hk) hc
theorem h_index_bound (cfg : Config) {e r c} (he : e < 2) (hr : r < cfg.input.m) (hc : c < cfg.input.n) :
    (e*cfg.input.m+r)*cfg.input.n+c < (2*cfg.input.m)*cfg.input.n := matrix_index_lt (matrix_index_lt he hr) hc

theorem w_address (i : Inputs) (e k c : Nat) :
    wBase i e+4*c+(4*i.n)*k = i.w+4*((e*i.k+k)*i.n+c) := by unfold wBase; ring
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
  · intro k hk
    have hi := x_index_bound cfg ha.1 hk
    have hend := cfg.xEnd (by have := ha.2; omega)
    change cfg.input.x+4*(row cfg.geometry.block id*cfg.input.k)+4*k < 2^64
    omega
  · intro k hk
    change wBase cfg.input e+4*col cfg.geometry.block id+(4*cfg.input.n)*k < 2^64
    rw [w_address]
    have hi := w_index_bound cfg he hk ha.2
    have hend := cfg.wEnd (by have := ha.1; omega)
    omega

theorem r_footprint (cfg : Config) {r offset} (hr : r < cfg.input.m) (hn : 0 < cfg.input.n) (ho : offset < 4) :
    ((rLoc cfg r).add offset).address < 2^64 := by
  have he := cfg.rEnd hn
  simp only [rLoc,Location.add]
  omega
theorem x_footprint (cfg : Config) {r k offset} (hr : r < cfg.input.m) (hk : k < cfg.input.k)
    (hn : 0 < cfg.input.n) (ho : offset < 4) : ((xLoc cfg r k).add offset).address < 2^64 := by
  have hi := x_index_bound cfg hr hk
  have he := cfg.xEnd hn
  simp only [xLoc,Location.add]
  omega
theorem w_footprint (cfg : Config) {e k c offset} (he : e < 2) (hk : k < cfg.input.k) (hc : c < cfg.input.n)
    (hm : 0 < cfg.input.m) (ho : offset < 4) : ((wLoc cfg e k c).add offset).address < 2^64 := by
  have hi := w_index_bound cfg he hk hc
  have hend := cfg.wEnd hm
  simp only [wLoc,Location.add]
  omega
theorem h_footprint (cfg : Config) {e r c offset} (he : e < 2) (hr : r < cfg.input.m) (hc : c < cfg.input.n)
    (ho : offset < 4) : ((hLoc cfg e r c).add offset).address < 2^64 := by
  have hi := h_index_bound cfg he hr hc
  have hend := cfg.hEnd
  simp only [hLoc,Location.add]
  omega

theorem r_aligned (cfg : Config) {r} (hr : r < cfg.input.m) (hn : 0 < cfg.input.n) :
    (rLoc cfg r).address % 4 = 0 := by
  simp [rLoc,Nat.add_mod,cfg.rAligned (by omega) hn]
theorem x_aligned (cfg : Config) {r k} (hr : r < cfg.input.m) (hk : k < cfg.input.k) (hn : 0 < cfg.input.n) :
    (xLoc cfg r k).address % 4 = 0 := by
  simp [xLoc,Nat.add_mod,cfg.xAligned (by omega) hn (by omega)]
theorem w_aligned (cfg : Config) {e k c} (hk : k < cfg.input.k) (hc : c < cfg.input.n) (hm : 0 < cfg.input.m) :
    (wLoc cfg e k c).address % 4 = 0 := by
  simp [wLoc,Nat.add_mod,cfg.wAligned hm (by omega) (by omega)]
theorem h_aligned (cfg : Config) {e r c} (hr : r < cfg.input.m) (hc : c < cfg.input.n) :
    (hLoc cfg e r c).address % 4 = 0 := by
  simp [hLoc,Nat.add_mod,cfg.hAligned (by omega) (by omega)]

def Initialized (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (initial : Scalar.ByteMap) : Prop :=
  (∀ r, r < cfg.input.m → 0 < cfg.input.n → RepresentsU32 initial (rLoc cfg r) (Moe.selected gates r)) ∧
  (∀ r k, r < cfg.input.m → k < cfg.input.k → 0 < cfg.input.n → RepresentsReal .f32 initial (xLoc cfg r k) (x r k)) ∧
  (∀ e k c, e < 2 → k < cfg.input.k → c < cfg.input.n → 0 < cfg.input.m →
    RepresentsReal .f32 initial (wLoc cfg e k c) (weights e k c))
def Pre (cfg : Config) (gates x : Moe.Matrix) (weights : Moe.Weights) (launch : Scalar.Launch) : Prop :=
  launch.geometry = cfg.geometry ∧ Params cfg.input launch.params ∧ Initialized cfg gates x weights launch.initial

end
end Ptx.MoeExpertsEvent
