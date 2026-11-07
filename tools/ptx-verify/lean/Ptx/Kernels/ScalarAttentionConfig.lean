import Ptx.Kernels.ScalarAttentionSourceTrace
import Ptx.Scalar.Regions

/-! Whole-launch layout for the actual scalar attention source. Read-only regions
may overlap if their symbolic initial representations agree. When no thread can
read (including N=0), no read-region bounds, alignment or separation are required.
These mathematical byte bounds are not physical allocation/runtime guarantees. -/
namespace Ptx.ScalarAttentionEvent
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttention Ptx.ScalarAttentionInit
noncomputable section

def ReadsEnabled (i : Inputs) : Prop := 0 < i.m ∧ 0 < i.dim ∧ 0 < i.n

instance instDecidableReadsEnabled (i : Inputs) : Decidable (ReadsEnabled i) :=
  inferInstanceAs (Decidable (0 < i.m ∧ 0 < i.dim ∧ 0 < i.n))

structure ReadLayout (i : Inputs) : Prop where
  qEnd : i.q+4*(i.m*i.dim) ≤ 2^64
  keyEnd : i.key+4*(i.n*i.dim) ≤ 2^64
  valueEnd : i.value+4*(i.n*i.dim) ≤ 2^64
  scaleEnd : i.scale+4 ≤ 2^64
  qAligned : i.q % 4 = 0
  keyAligned : i.key % 4 = 0
  valueAligned : i.value % 4 = 0
  scaleAligned : i.scale % 4 = 0
  separateQ : WordsDisjoint i.q (i.m*i.dim) i.output (i.m*i.dim)
  separateKey : WordsDisjoint i.key (i.n*i.dim) i.output (i.m*i.dim)
  separateValue : WordsDisjoint i.value (i.n*i.dim) i.output (i.m*i.dim)
  separateScale : WordsDisjoint i.scale 1 i.output (i.m*i.dim)

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
  coversCols : input.dim ≤ geometry.grid.x*geometry.block.x
  outputEnd : input.output+4*(input.m*input.dim) ≤ 2^64
  outputAligned : 0 < input.m → 0 < input.dim → input.output % 4 = 0
  readLayout : ReadsEnabled input → ReadLayout input

def context (cfg : Config) (params : Bindings) (id : ThreadId) : Scalar.Context :=
  {id := id,params := params,block := cfg.geometry.block}
def qLoc (cfg : Config) (r k : Nat) : Location := ⟨.global,cfg.input.q+4*(r*cfg.input.dim+k)⟩
def keyLoc (cfg : Config) (j k : Nat) : Location := ⟨.global,cfg.input.key+4*(j*cfg.input.dim+k)⟩
def valueLoc (cfg : Config) (j c : Nat) : Location := ⟨.global,cfg.input.value+4*(j*cfg.input.dim+c)⟩
def outputLoc (cfg : Config) (r c : Nat) : Location := ⟨.global,cfg.input.output+4*(r*cfg.input.dim+c)⟩
def scaleLoc (cfg : Config) : Location := ⟨.global,cfg.input.scale⟩

def Active (cfg : Config) (id : ThreadId) : Prop :=
  row cfg.geometry.block id < cfg.input.m ∧ col cfg.geometry.block id < cfg.input.dim

theorem reads_enabled {cfg : Config} {id : ThreadId} (ha : Active cfg id) (hn : 0 < cfg.input.n) :
    ReadsEnabled cfg.input := ⟨by have := ha.1; omega,by have := ha.2; omega,hn⟩

theorem index_bounds (cfg : Config) {id : ThreadId} (hv : id.Valid cfg.geometry) (params : Bindings) :
    IndexBounds (context cfg params id) :=
  Scalar.Indexing.bounds_of_launch cfg.gridX32 cfg.gridY32 cfg.blockX32 cfg.blockY32
    cfg.extentX32 cfg.extentY32 hv params

theorem q_index_bound (cfg : Config) {r k : Nat} (hr : r < cfg.input.m) (hk : k < cfg.input.dim) :
    r*cfg.input.dim+k < cfg.input.m*cfg.input.dim := matrix_index_lt hr hk

theorem key_index_bound (cfg : Config) {j k : Nat} (hj : j < cfg.input.n) (hk : k < cfg.input.dim) :
    j*cfg.input.dim+k < cfg.input.n*cfg.input.dim := matrix_index_lt hj hk

theorem output_index_bound (cfg : Config) {r c : Nat} (hr : r < cfg.input.m) (hc : c < cfg.input.dim) :
    r*cfg.input.dim+c < cfg.input.m*cfg.input.dim := matrix_index_lt hr hc

theorem output_bound (cfg : Config) (params : Bindings) {id : ThreadId} (ha : Active cfg id) :
    outputAddress cfg.input (context cfg params id) < 2^64 := by
  have hi := output_index_bound cfg ha.1 ha.2
  have hend := cfg.outputEnd
  change cfg.input.output+4*(row cfg.geometry.block id*cfg.input.dim+col cfg.geometry.block id) < 2^64
  omega

theorem address_bounds (cfg : Config) (params : Bindings) {id : ThreadId}
    (ha : Active cfg id) (hn : 0 < cfg.input.n) : AddressBounds cfg.input (context cfg params id) := by
  have hl := cfg.readLayout (reads_enabled ha hn)
  constructor
  · exact output_bound cfg params ha
  · intro k hk
    have hi := q_index_bound cfg ha.1 hk
    have hend := hl.qEnd
    change cfg.input.q+4*(row cfg.geometry.block id*cfg.input.dim)+4*k < 2^64
    omega
  · intro j k hj hk
    have hi := key_index_bound cfg hj hk
    have hend := hl.keyEnd
    rw [Nat.mul_assoc,Nat.mul_comm cfg.input.dim j]
    omega
  · intro j hj
    have hi := key_index_bound cfg hj ha.2
    have hend := hl.valueEnd
    change cfg.input.value+4*col cfg.geometry.block id+4*cfg.input.dim*j < 2^64
    rw [Nat.mul_assoc,Nat.mul_comm cfg.input.dim j]
    omega

theorem q_footprint (cfg : Config) (he : ReadsEnabled cfg.input) {r k offset : Nat}
    (hr : r < cfg.input.m) (hk : k < cfg.input.dim) (ho : offset < 4) :
    ((qLoc cfg r k).add offset).address < 2^64 := by
  have hi := q_index_bound cfg hr hk
  have hend := (cfg.readLayout he).qEnd
  simp only [qLoc,Location.add]
  omega

theorem key_footprint (cfg : Config) (he : ReadsEnabled cfg.input) {j k offset : Nat}
    (hj : j < cfg.input.n) (hk : k < cfg.input.dim) (ho : offset < 4) :
    ((keyLoc cfg j k).add offset).address < 2^64 := by
  have hi := key_index_bound cfg hj hk
  have hend := (cfg.readLayout he).keyEnd
  simp only [keyLoc,Location.add]
  omega

theorem value_footprint (cfg : Config) (he : ReadsEnabled cfg.input) {j c offset : Nat}
    (hj : j < cfg.input.n) (hc : c < cfg.input.dim) (ho : offset < 4) :
    ((valueLoc cfg j c).add offset).address < 2^64 := by
  have hi := key_index_bound cfg hj hc
  have hend := (cfg.readLayout he).valueEnd
  simp only [valueLoc,Location.add]
  omega

theorem scale_footprint (cfg : Config) (he : ReadsEnabled cfg.input) {offset : Nat} (ho : offset < 4) :
    ((scaleLoc cfg).add offset).address < 2^64 := by
  have hend := (cfg.readLayout he).scaleEnd
  simp only [scaleLoc,Location.add]
  omega

theorem output_footprint (cfg : Config) {r c offset : Nat}
    (hr : r < cfg.input.m) (hc : c < cfg.input.dim) (ho : offset < 4) :
    ((outputLoc cfg r c).add offset).address < 2^64 := by
  have hi := output_index_bound cfg hr hc
  have hend := cfg.outputEnd
  simp only [outputLoc,Location.add]
  omega

theorem q_aligned (cfg : Config) (he : ReadsEnabled cfg.input) (r k : Nat) :
    (qLoc cfg r k).address % 4 = 0 := by simp [qLoc,Nat.add_mod,(cfg.readLayout he).qAligned]
theorem key_aligned (cfg : Config) (he : ReadsEnabled cfg.input) (j k : Nat) :
    (keyLoc cfg j k).address % 4 = 0 := by simp [keyLoc,Nat.add_mod,(cfg.readLayout he).keyAligned]
theorem value_aligned (cfg : Config) (he : ReadsEnabled cfg.input) (j c : Nat) :
    (valueLoc cfg j c).address % 4 = 0 := by simp [valueLoc,Nat.add_mod,(cfg.readLayout he).valueAligned]
theorem scale_aligned (cfg : Config) (he : ReadsEnabled cfg.input) :
    (scaleLoc cfg).address % 4 = 0 := (cfg.readLayout he).scaleAligned
theorem output_aligned (cfg : Config) {r c : Nat} (hr : r < cfg.input.m) (hc : c < cfg.input.dim) :
    (outputLoc cfg r c).address % 4 = 0 := by
  have hm : 0 < cfg.input.m := by omega
  have hd : 0 < cfg.input.dim := by omega
  simp [outputLoc,Nat.add_mod,cfg.outputAligned hm hd]

def Initialized (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (initial : Scalar.ByteMap) : Prop :=
  ReadsEnabled cfg.input →
    RepresentsReal .f32 initial (scaleLoc cfg) scale ∧
    (∀ r k, r < cfg.input.m → k < cfg.input.dim → RepresentsReal .f32 initial (qLoc cfg r k) (q r k)) ∧
    (∀ j k, j < cfg.input.n → k < cfg.input.dim → RepresentsReal .f32 initial (keyLoc cfg j k) (key j k)) ∧
    (∀ j c, j < cfg.input.n → c < cfg.input.dim → RepresentsReal .f32 initial (valueLoc cfg j c) (value j c))

def Pre (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (launch : Scalar.Launch) : Prop :=
  launch.geometry = cfg.geometry ∧ Params cfg.input launch.params ∧ Initialized cfg q key value scale launch.initial

end
end Ptx.ScalarAttentionEvent
