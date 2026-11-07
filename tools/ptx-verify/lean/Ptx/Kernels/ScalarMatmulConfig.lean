import Ptx.Kernels.ScalarMatmulThread
import Ptx.Scalar.Regions

/-! Launch/layout preconditions for the matrix event-model contract. Full word
footprints are bounded; C is disjoint from the two read-only input regions.
A/B may alias, subject to agreement of their represented initial values.
Physical allocation/runtime and full PTX correspondence remain external duties.
-/
namespace Ptx.ScalarMatmulEvent
open Ptx.ISA Ptx.Scalar Ptx.ScalarMatmul Ptx.ScalarMatmulInit
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
  aEnd : input.a+4*(input.m*input.k) ≤ 2^64
  bEnd : input.b+4*(input.k*input.n) ≤ 2^64
  cEnd : input.c+4*(input.m*input.n) ≤ 2^64
  aAligned : input.a % 4 = 0
  bAligned : input.b % 4 = 0
  cAligned : input.c % 4 = 0
  separateA : WordsDisjoint input.a (input.m*input.k) input.c (input.m*input.n)
  separateB : WordsDisjoint input.b (input.k*input.n) input.c (input.m*input.n)

def context (cfg : Config) (params : Bindings) (id : ThreadId) : Scalar.Context :=
  {id := id,params := params,block := cfg.geometry.block}
def aLoc (cfg : Config) (r k : Nat) : Location := ⟨.global,cfg.input.a+4*(r*cfg.input.k+k)⟩
def bLoc (cfg : Config) (k c : Nat) : Location := ⟨.global,cfg.input.b+4*(k*cfg.input.n+c)⟩
def cLoc (cfg : Config) (r c : Nat) : Location := ⟨.global,cfg.input.c+4*(r*cfg.input.n+c)⟩

def Active (cfg : Config) (id : ThreadId) : Prop :=
  row cfg.geometry.block id < cfg.input.m ∧ col cfg.geometry.block id < cfg.input.n

theorem index_bounds (cfg : Config) {id : ThreadId} (hv : id.Valid cfg.geometry) (params : Bindings) :
    IndexBounds (context cfg params id) :=
  index_bounds_of_launch cfg.gridX32 cfg.gridY32 cfg.blockX32 cfg.blockY32 cfg.extentX32 cfg.extentY32 hv params

theorem a_index_bound (cfg : Config) {r k : Nat} (hr : r < cfg.input.m) (hk : k < cfg.input.k) :
    r*cfg.input.k+k < cfg.input.m*cfg.input.k := matrix_index_lt hr hk

theorem b_index_bound (cfg : Config) {k c : Nat} (hk : k < cfg.input.k) (hc : c < cfg.input.n) :
    k*cfg.input.n+c < cfg.input.k*cfg.input.n := matrix_index_lt hk hc

theorem c_index_bound (cfg : Config) {r c : Nat} (hr : r < cfg.input.m) (hc : c < cfg.input.n) :
    r*cfg.input.n+c < cfg.input.m*cfg.input.n := matrix_index_lt hr hc

theorem address_bounds (cfg : Config) (params : Bindings) {id : ThreadId} (ha : Active cfg id) :
    AddressBounds cfg.input (context cfg params id) := by
  have hc := c_index_bound cfg ha.1 ha.2
  constructor
  · change cfg.input.c+4*(row cfg.geometry.block id*cfg.input.n+col cfg.geometry.block id) < 2^64
    have hend := cfg.cEnd
    omega
  · intro k hk
    have hi := a_index_bound cfg ha.1 hk
    change cfg.input.a+4*(row cfg.geometry.block id*cfg.input.k)+4*k < 2^64
    have hend := cfg.aEnd
    omega
  · intro k hk
    have hi := b_index_bound cfg hk ha.2
    change cfg.input.b+4*col cfg.geometry.block id+(4*cfg.input.n)*k < 2^64
    have hend := cfg.bEnd
    have hsame : 4*col cfg.geometry.block id+(4*cfg.input.n)*k =
        4*(k*cfg.input.n+col cfg.geometry.block id) := by
      rw [Nat.mul_assoc,Nat.mul_comm cfg.input.n k,Nat.mul_add]
      omega
    rw [Nat.add_assoc,hsame]
    omega

theorem a_footprint (cfg : Config) {r k offset : Nat} (hr : r < cfg.input.m) (hk : k < cfg.input.k) (ho : offset < 4) :
    ((aLoc cfg r k).add offset).address < 2^64 := by
  have hi := a_index_bound cfg hr hk
  have hend := cfg.aEnd
  simp only [aLoc,Location.add]
  omega

theorem b_footprint (cfg : Config) {k c offset : Nat} (hk : k < cfg.input.k) (hc : c < cfg.input.n) (ho : offset < 4) :
    ((bLoc cfg k c).add offset).address < 2^64 := by
  have hi := b_index_bound cfg hk hc
  have hend := cfg.bEnd
  simp only [bLoc,Location.add]
  omega

theorem c_footprint (cfg : Config) {r c offset : Nat} (hr : r < cfg.input.m) (hc : c < cfg.input.n) (ho : offset < 4) :
    ((cLoc cfg r c).add offset).address < 2^64 := by
  have hi := c_index_bound cfg hr hc
  have hend := cfg.cEnd
  simp only [cLoc,Location.add]
  omega

theorem a_aligned (cfg : Config) (r k : Nat) : (aLoc cfg r k).address % 4 = 0 := by
  simp [aLoc,Nat.add_mod,cfg.aAligned]

theorem b_aligned (cfg : Config) (k c : Nat) : (bLoc cfg k c).address % 4 = 0 := by
  simp [bLoc,Nat.add_mod,cfg.bAligned]

theorem c_aligned (cfg : Config) (r c : Nat) : (cLoc cfg r c).address % 4 = 0 := by
  simp [cLoc,Nat.add_mod,cfg.cAligned]

def Initialized (cfg : Config) (a b : Matrix) (initial : Scalar.ByteMap) : Prop :=
  (∀ r k, r < cfg.input.m → k < cfg.input.k → RepresentsReal .f32 initial (aLoc cfg r k) (a r k)) ∧
  (∀ k c, k < cfg.input.k → c < cfg.input.n → RepresentsReal .f32 initial (bLoc cfg k c) (b k c))

def Pre (cfg : Config) (a b : Matrix) (launch : Scalar.Launch) : Prop :=
  launch.geometry = cfg.geometry ∧ Params cfg.input launch.params ∧ Initialized cfg a b launch.initial

end
end Ptx.ScalarMatmulEvent
