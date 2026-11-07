import Std

/-! Shared program data for the integer subset, including unsigned logical right
shift. The operational and event interpreters consume the same generated
program data; earlier instruction forms retain their meaning. New instruction forms must acquire explicit
types, qualifiers, and semantics before the frontend accepts them. -/
namespace Ptx

inductive Space | global | shared deriving Repr, DecidableEq, BEq
deriving instance ReflBEq, LawfulBEq for Space
inductive Operand | imm (n : Nat) | reg (r : String) | tid deriving Repr, DecidableEq
structure Address where
  base : Operand
  offset : Nat := 0
  deriving Repr, DecidableEq
inductive BinOp | add | sub | mul | shr deriving Repr, DecidableEq
inductive Cmp | lt | ge | eq deriving Repr, DecidableEq
inductive Instr where
  | mov (width : Nat) (dst : String) (a : Operand)
  | param (width : Nat) (dst name : String)
  | bin (op : BinOp) (inputWidth outputWidth : Nat) (dst : String) (a b : Operand)
  | setp (cmp : Cmp) (dst : String) (a b : Operand)
  | load (space : Space) (dst : String) (addr : Address)
  | store (space : Space) (addr : Address) (value : Operand)
  | branch (pred : String) (positive : Bool) (target : Nat)
  | jump (target : Nat)
  | barrier (id : Nat)
  | ret
  deriving Repr, DecidableEq

end Ptx
