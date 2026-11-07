import Ptx.Scalar.Memory
import Ptx.Ampere.MmaFragments
import Mathlib.Algebra.BigOperators.Fin

/-! Independent exact-real specification for tiled matmul. A is row-major f16,
B is column-major f16, C is row-major f32. Empty outputs/zero K require no unused
input representations or input/output separation. This defines proof obligations,
not a correctness theorem for the generated source or IEEE execution. -/
namespace Ptx.AmpereTiledSpec
open Ptx.ISA
open scoped BigOperators
noncomputable section

abbrev Matrix := Nat → Nat → ℝ
structure Config where
  m : Nat
  n : Nat
  k : Nat
  a : Nat
  b : Nat
  c : Nat
  arenaBytes : Nat

def Active (cfg : Config) : Prop := 0 < cfg.m ∧ 0 < cfg.n
def Disjoint (a lenA b lenB : Nat) : Prop := a+lenA ≤ b ∨ b+lenB ≤ a
structure Layout (cfg : Config) : Prop where
  dimensions : cfg.m < 2^32 ∧ cfg.n < 2^32 ∧ cfg.k < 2^32
  tiles : cfg.m%16 = 0 ∧ cfg.n%8 = 0 ∧ cfg.k%16 = 0
  pointers : cfg.a < 2^64 ∧ cfg.b < 2^64 ∧ cfg.c < 2^64
  arena : cfg.arenaBytes ≤ 2^64
  output : Active cfg → cfg.c+4*(cfg.m*cfg.n) ≤ cfg.arenaBytes ∧ cfg.c%4 = 0
  inputs : Active cfg → 0 < cfg.k →
    cfg.a+2*(cfg.m*cfg.k) ≤ cfg.arenaBytes ∧ cfg.b+2*(cfg.n*cfg.k) ≤ cfg.arenaBytes ∧
    cfg.a%8 = 0 ∧ cfg.b%8 = 0 ∧
    Disjoint cfg.a (2*(cfg.m*cfg.k)) cfg.c (4*(cfg.m*cfg.n)) ∧
    Disjoint cfg.b (2*(cfg.n*cfg.k)) cfg.c (4*(cfg.m*cfg.n))

def geometry (cfg : Config) : Geometry := ⟨⟨max 1 (cfg.n/8),max 1 (cfg.m/16),1⟩,⟨4,8,1⟩⟩
def params (cfg : Config) : Bindings :=
  [("A",cfg.a),("B",cfg.b),("C",cfg.c),("M",cfg.m),("N",cfg.n),("K",cfg.k)]
def aLocation (cfg : Config) (row k : Nat) : Location := ⟨.global,cfg.a+2*(row*cfg.k+k)⟩
def bLocation (cfg : Config) (k col : Nat) : Location := ⟨.global,cfg.b+2*(col*cfg.k+k)⟩
def cLocation (cfg : Config) (row col : Nat) : Location := ⟨.global,cfg.c+4*(row*cfg.n+col)⟩
def Input (cfg : Config) (a b : Matrix) (initial : Ptx.Event.ByteMap Symbolic.Byte) : Prop :=
  Active cfg →
    (∀ row k, row < cfg.m → k < cfg.k → Scalar.RepresentsReal .f16 initial (aLocation cfg row k) (a row k)) ∧
    (∀ k col, k < cfg.k → col < cfg.n → Scalar.RepresentsReal .f16 initial (bLocation cfg k col) (b k col))
def Pre (cfg : Config) (a b : Matrix) (launch : Scalar.Launch) : Prop :=
  Layout cfg ∧ Input cfg a b launch.initial ∧ launch.geometry = geometry cfg ∧ launch.params = params cfg

def product (a b : Matrix) (row col k : Nat) : ℝ := ∑ t ∈ Finset.range k, a row t*b t col
def partialProduct (a b : Matrix) (row col tiles : Nat) : ℝ := product a b row col (16*tiles)
def domain (cfg : Config) : List Location := (List.range cfg.arenaBytes).map (fun address => ⟨.global,address⟩)
def InOutput (cfg : Config) (loc : Location) : Prop :=
  loc.space = .global ∧ cfg.c ≤ loc.address ∧ loc.address < cfg.c+4*(cfg.m*cfg.n)
def Post (cfg : Config) (a b : Matrix) (initial output : Ptx.Event.ByteMap Symbolic.Byte) : Prop :=
  (∀ row col, row < cfg.m → col < cfg.n →
    Scalar.RepresentsReal .f32 output (cLocation cfg row col) (product a b row col cfg.k)) ∧
  (∀ loc ∈ domain cfg, ¬ InOutput cfg loc → output loc = initial loc)

theorem geometry_valid (cfg : Config) : (geometry cfg).Valid := by
  simp only [geometry,Geometry.Valid,Dim3.Positive]
  omega

theorem domain_global {cfg loc} (hl : loc ∈ domain cfg) : loc.space = .global := by
  obtain ⟨address,_,rfl⟩ := List.mem_map.mp hl
  rfl

theorem output_element_index {cfg : Config} {row col : Nat} (hr : row < cfg.m) (hc : col < cfg.n) :
    row*cfg.n+col < cfg.m*cfg.n := by
  have hh := Nat.mul_le_mul_right cfg.n (Nat.succ_le_of_lt hr)
  rw [Nat.succ_mul] at hh
  omega

theorem output_byte_in_domain {cfg : Config} (hl : Layout cfg) {row col offset : Nat}
    (hr : row < cfg.m) (hc : col < cfg.n) (ho : offset < 4) :
    ((cLocation cfg row col).add offset) ∈ domain cfg := by
  have hactive : Active cfg := ⟨by omega,by omega⟩
  have hbound := (hl.output hactive).1
  have hindex := output_element_index hr hc
  exact List.mem_map.mpr ⟨cfg.c+4*(row*cfg.n+col)+offset,List.mem_range.mpr (by omega),rfl⟩

theorem zero_k_product (a b : Matrix) (row col : Nat) : product a b row col 0 = 0 := by simp [product]

theorem empty_output_no_input {cfg : Config} (he : cfg.m = 0 ∨ cfg.n = 0)
    (a b : Matrix) (initial : Ptx.Event.ByteMap Symbolic.Byte) : Input cfg a b initial := by
  intro ha
  rcases he with hm | hn <;> rcases ha with ⟨ha,hb⟩ <;> omega

theorem zero_k_no_input {cfg : Config} (hk : cfg.k = 0)
    (a b : Matrix) (initial : Ptx.Event.ByteMap Symbolic.Byte) : Input cfg a b initial := by
  intro _
  constructor
  · intro row k _ hlt
    omega
  · intro k col hlt _
    omega

theorem block_accumulation_step (a b : Matrix) (row col tiles : Nat) :
    partialProduct a b row col (tiles+1) = partialProduct a b row col tiles +
      ∑ t : Fin 16, a row (16*tiles+t.val)*b (16*tiles+t.val) col := by
  simp only [partialProduct,product,Nat.mul_add,Nat.mul_one,Finset.sum_range_add]
  congr 1

def tileA (a : Matrix) (tileRow step : Nat) : Ampere.Mma.ACoord → ℝ :=
  fun p => a (16*tileRow+p.1.val) (16*step+p.2.val)
def tileB (b : Matrix) (tileCol step : Nat) : Ampere.Mma.BCoord → ℝ :=
  fun p => b (16*step+p.1.val) (8*tileCol+p.2.val)
def tileC (a b : Matrix) (tileRow tileCol steps : Nat) : Ampere.Mma.CCoord → ℝ :=
  fun p => partialProduct a b (16*tileRow+p.1.val) (8*tileCol+p.2.val) steps

theorem mma_accumulation_step (a b : Matrix) (tileRow tileCol steps : Nat) :
    Ampere.Mma.matrixStep (tileA a tileRow steps) (tileB b tileCol steps)
      (tileC a b tileRow tileCol steps) = tileC a b tileRow tileCol (steps+1) := by
  funext p
  simpa only [Ampere.Mma.matrixStep,tileA,tileB,tileC] using
    (block_accumulation_step a b (16*tileRow+p.1.val) (8*tileCol+p.2.val) steps).symm

theorem full_product_from_tiles {cfg : Config} (hl : Layout cfg) (a b : Matrix) (row col : Nat) :
    partialProduct a b row col (cfg.k/16) = product a b row col cfg.k := by
  have hk := hl.tiles.2.2
  have he : 16*(cfg.k/16) = cfg.k := by omega
  simp only [partialProduct,he]

end
end Ptx.AmpereTiledSpec
