import Ptx.ISA.Fragments
import Ptx.Scalar.IntegerMemory

/-! Independent byte-copy specification and represented input for the actual
sixteen-byte helper. A finite global arena is observed, including its frame.
This is not a specification for the pending tiled MMA acceptance case. -/
namespace Ptx.CpAsyncCopySpec
open Ptx.ISA
noncomputable section

structure Config where
  src : Nat
  dst : Nat
  arenaBytes : Nat

def Layout (cfg : Config) : Prop :=
  cfg.arenaBytes ≤ 2^64 ∧ cfg.src+16 ≤ cfg.arenaBytes ∧ cfg.dst+16 ≤ cfg.arenaBytes ∧
  cfg.src % 16 = 0 ∧ cfg.dst % 4 = 0 ∧ (cfg.src+16 ≤ cfg.dst ∨ cfg.dst+16 ≤ cfg.src)

def Input (cfg : Config) (initial : Ptx.Event.ByteMap Symbolic.Byte) : Prop :=
  ∃ values : Fin 4 → Nat, ∀ i : Fin 4, values i < 2^32 ∧
    Scalar.RepresentsU32 initial ⟨.global,cfg.src+4*i.val⟩ (values i)

def domain (cfg : Config) : List Location := (List.range cfg.arenaBytes).map (fun addr => ⟨.global,addr⟩)
def InOutput (cfg : Config) (loc : Location) : Prop :=
  loc.space = .global ∧ cfg.dst ≤ loc.address ∧ loc.address < cfg.dst+16
def Post (cfg : Config) (initial output : Ptx.Event.ByteMap Symbolic.Byte) : Prop :=
  (∀ offset, offset < 16 → output ⟨.global,cfg.dst+offset⟩ = initial ⟨.global,cfg.src+offset⟩) ∧
  (∀ loc ∈ domain cfg, ¬ InOutput cfg loc → output loc = initial loc)

theorem domain_global {cfg loc} (hl : loc ∈ domain cfg) : loc.space = .global := by
  obtain ⟨addr,_,rfl⟩ := List.mem_map.mp hl
  rfl
theorem output_in_domain {cfg : Config} (hl : Layout cfg) (offset : Nat) (ho : offset < 16) :
    (⟨.global,cfg.dst+offset⟩ : Location) ∈ domain cfg := by
  exact List.mem_map.mpr ⟨cfg.dst+offset,List.mem_range.mpr (by rcases hl with ⟨_,_,hd,_⟩; omega),rfl⟩

end
end Ptx.CpAsyncCopySpec
