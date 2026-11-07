import Ptx.Generated.ShuffleUp
import Ptx.Generated.ShuffleDown
import Ptx.Generated.ShuffleBfly
import Ptx.Generated.ShuffleIdx
import Ptx.Shuffle.Local
import Ptx.Shuffle.Source

/-! One source skeleton for the four mechanically translated exported probes.
Every mode is proved equal to its generated program. Raw finite-width index
arithmetic is retained; geometric interpretation requires separate bounds. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

def generated : Mode → List Shuffle.Instr
  | .up => Generated.shuffle_up.program
  | .down => Generated.shuffle_down.program
  | .bfly => Generated.shuffle_bfly.program
  | .idx => Generated.shuffle_idx.program
def code (mode : Mode) : List Shuffle.Instr := Generated.shuffle_up.program.set 15
  (.shfl mode "%r11" (some "%p") (.reg "%r10") (.reg "%r0") (.reg "%r1") (.reg "%r2"))

theorem mechanical_program (mode : Mode) : code mode = generated mode := by cases mode <;> rfl

theorem mechanically_typed (mode : Mode) : Shuffle.ProgramTyped 70 Generated.shuffle_up.registerDeclarations
    Generated.shuffle_up.parameters (code mode) := by
  cases mode
  · exact Generated.shuffle_up.checked.valid
  · exact Generated.shuffle_down.checked.valid
  · exact Generated.shuffle_bfly.checked.valid
  · exact Generated.shuffle_idx.checked.valid

structure Inputs where
  out : Nat
  b : Nat
  c : Nat
  mask : Nat
  base : Nat
structure Params (input : Inputs) (params : Bindings) : Prop where
  out : lookup "Out" params = some input.out
  b : lookup "B" params = some input.b
  c : lookup "C" params = some input.c
  mask : lookup "Mask" params = some input.mask
  base : lookup "Base" params = some input.base

def w32 (value : Nat) := wrap 32 value
def w64 (value : Nat) := wrap 64 value
@[simp] theorem w32_idem (value : Nat) : w32 (w32 value) = w32 value := Nat.mod_mod _ _
@[simp] theorem w64_idem (value : Nat) : w64 (w64 value) = w64 value := Nat.mod_mod _ _
def yzProduct (ctx : Scalar.Context) := w32 (w32 ctx.block.y * w32 ctx.id.tid.z)
def yzIndex (ctx : Scalar.Context) := w32 (yzProduct ctx + w32 ctx.id.tid.y)
def xProduct (ctx : Scalar.Context) := w32 (yzIndex ctx * w32 ctx.block.x)
def rawIndex (ctx : Scalar.Context) := w32 (xProduct ctx + w32 ctx.id.tid.x)
def inputWord (input : Inputs) (ctx : Scalar.Context) := w32 (w32 input.base + rawIndex ctx)
def assignments (input : Inputs) (ctx : Scalar.Context) : List (String × Nat) := [
  ("%rd0",w64 input.out),("%r0",w32 input.b),("%r1",w32 input.c),("%r2",w32 input.mask),("%r3",w32 input.base),
  ("%r4",w32 ctx.id.tid.x),("%r5",w32 ctx.id.tid.y),("%r6",w32 ctx.id.tid.z),
  ("%r7",w32 ctx.block.x),("%r8",w32 ctx.block.y),("%r9",yzProduct ctx),("%r9",yzIndex ctx),
  ("%r9",xProduct ctx),("%r9",rawIndex ctx),("%r10",inputWord input ctx)]
def prefixState (input : Inputs) (ctx : Scalar.Context) (n : Nat) : Shuffle.State :=
  ((assignments input ctx).take n).foldl (fun state item => Shuffle.intAssign state item.1 item.2) {}
def groupKey (mode : Mode) (input : Inputs) : Key := ⟨mode,w32 input.mask⟩
def record (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (value : Nat) (predicate : Bool) : Record :=
  ⟨groupKey mode input,0,15,inputWord input ctx,w32 input.b,w32 input.c,w32 value,predicate⟩
def afterShuffle (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (value : Nat) (predicate : Bool) : Shuffle.State :=
  ⟨writeResult (prefixState input ctx 15).base "%r11" (some "%p") value predicate,1,[(groupKey mode input,1)]⟩
def flagged (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (value : Nat) (predicate : Bool) : Shuffle.State :=
  let state := Shuffle.intAssign (afterShuffle mode input ctx value predicate) "%r12" 0
  if predicate then Shuffle.intAssign (Shuffle.intPC state 19) "%r12" 1 else Shuffle.intPC (Shuffle.intPC state 18) 20
def address (input : Inputs) (ctx : Scalar.Context) := w64 (w64 input.out + w64 (rawIndex ctx * 8))
def addressed (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (value : Nat) (predicate : Bool) : Shuffle.State :=
  Shuffle.intAssign (Shuffle.intAssign (flagged mode input ctx value predicate) "%rd1" (w64 (rawIndex ctx * 8))) "%rd2" (address input ctx)
def advanceState (state : Shuffle.State) : Shuffle.State :=
  {state with base := Scalar.finishInteger state.base {state.base.core with thread := advance state.base.core.thread}}
def beforeRet (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (value : Nat) (predicate : Bool) : Shuffle.State :=
  advanceState (advanceState (addressed mode input ctx value predicate))
def finalState (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (value : Nat) (predicate : Bool) : Shuffle.State :=
  let state := beforeRet mode input ctx value predicate
  {state with base := Scalar.finishInteger state.base {state.base.core with thread := {state.base.core.thread with status := .done}}}
def outputLoc (input : Inputs) (ctx : Scalar.Context) (offset : Nat) : Location := ⟨.global,w64 (address input ctx + offset)⟩
def outputEvents (input : Inputs) (ctx : Scalar.Context) (value : Nat) (predicate : Bool) : List Shuffle.Kind := [
  .ordinary (.write (outputLoc input ctx 0) ((encodeU32 (w32 value)).map Symbolic.Byte.bits)),
  .ordinary (.write (outputLoc input ctx 4) ((encodeU32 (if predicate then 1 else 0)).map Symbolic.Byte.bits))]
def events (mode : Mode) (input : Inputs) (ctx : Scalar.Context) (value : Nat) (predicate : Bool) : List Shuffle.Kind :=
  .shuffle (record mode input ctx value predicate) :: outputEvents input ctx value predicate

end
end Ptx.Kernels.ShuffleProbe
