import Ptx.ISA.Syntax

/-! Grid identity and byte-addressed locations. This describes launch geometry;
it does not assert hardware limits, allocation validity, or runtime correctness. -/
namespace Ptx.ISA

structure Dim3 where
  x : Nat
  y : Nat
  z : Nat
  deriving Repr, DecidableEq, BEq
deriving instance ReflBEq, LawfulBEq for Dim3

def Dim3.zero : Dim3 := ⟨0, 0, 0⟩
def Dim3.one : Dim3 := ⟨1, 1, 1⟩
def Dim3.Positive (d : Dim3) : Prop := 0 < d.x ∧ 0 < d.y ∧ 0 < d.z
def Dim3.Within (index size : Dim3) : Prop :=
  index.x < size.x ∧ index.y < size.y ∧ index.z < size.z
def Dim3.volume (d : Dim3) : Nat := d.x * d.y * d.z
def Dim3.linear (index size : Dim3) : Nat :=
  index.x + size.x * (index.y + size.y * index.z)

structure Geometry where
  grid : Dim3
  block : Dim3
  deriving Repr, DecidableEq

def Geometry.Valid (g : Geometry) : Prop := g.grid.Positive ∧ g.block.Positive

structure ThreadId where
  cta : Dim3
  tid : Dim3
  deriving Repr, DecidableEq, BEq
deriving instance ReflBEq, LawfulBEq for ThreadId

def ThreadId.Valid (id : ThreadId) (g : Geometry) : Prop :=
  id.cta.Within g.grid ∧ id.tid.Within g.block

/-- Shared addresses are qualified by CTA identity; global addresses are not. -/
inductive AddressSpace
  | global
  | shared (cta : Dim3)
  deriving Repr, DecidableEq

structure Location where
  space : AddressSpace
  address : Nat
  deriving Repr, DecidableEq

def Location.resolve (space : Ptx.Space) (id : ThreadId) (address : Nat) : Location :=
  ⟨match space with | .global => .global | .shared => .shared id.cta, address⟩

def Location.add (loc : Location) (offset : Nat) : Location :=
  { loc with address := loc.address + offset }

theorem global_shared_across_ctas (a b : ThreadId) (address : Nat) :
    Location.resolve .global a address = Location.resolve .global b address := rfl

theorem shared_separate_ctas {a b : ThreadId} (h : a.cta ≠ b.cta) (x y : Nat) :
    Location.resolve .shared a x ≠ Location.resolve .shared b y := by
  intro heq
  have hs := congrArg Location.space heq
  exact h (AddressSpace.shared.inj hs)

end Ptx.ISA
