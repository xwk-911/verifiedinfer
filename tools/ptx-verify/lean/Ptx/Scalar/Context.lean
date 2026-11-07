import Ptx.Event.Thread

/-! Execution context for launch-dependent scalar instructions. The original
integer interpreter keeps its context unchanged. Legacy scalar call sites embed
that context with a unit block; launch-wide scalar provenance supplies the actual
block dimensions explicitly. This does not certify hardware launch limits.
-/
namespace Ptx.Scalar
open Ptx.ISA

structure Context extends Event.Context where
  block : Dim3 := .one

def Context.ofEvent (ctx : Event.Context) : Context := {toContext := ctx}
instance : Coe Event.Context Context := ⟨Context.ofEvent⟩

@[simp] theorem Context.ofEvent_toContext (ctx : Event.Context) : (Context.ofEvent ctx).toContext = ctx := rfl

inductive Axis | x | y | z deriving Repr, DecidableEq
def Axis.component : Axis → Dim3 → Nat
  | .x,d => d.x
  | .y,d => d.y
  | .z,d => d.z

inductive SpecialRegister
  | tid (axis : Axis)
  | ctaid (axis : Axis)
  | ntid (axis : Axis)
  deriving Repr, DecidableEq

def SpecialRegister.value (reg : SpecialRegister) (ctx : Context) : Nat :=
  match reg with
  | .tid axis => axis.component ctx.id.tid
  | .ctaid axis => axis.component ctx.id.cta
  | .ntid axis => axis.component ctx.block

end Ptx.Scalar
