import Ptx.Scalar.Syntax

/-! Fixed shfl.sync.{up,down,bfly,idx}.b32 extension for sm_70 and later.
The ordinary scalar slots retain their existing meaning and PC positions.
Typing alone proves neither source initialization nor cross-lane matching.
-/
namespace Ptx.Shuffle
open Ptx.ISA
noncomputable section

inductive Mode | up | down | bfly | idx deriving Repr, DecidableEq, BEq
deriving instance ReflBEq, LawfulBEq for Mode
abbrev Lane := BitVec 5
structure Selection where
  source : Lane
  predicate : Bool
  deriving Repr, DecidableEq

/-- The packed c operand uses bits 4:0 and 12:8. For up the documented
clamp is a lower bound; using a saturating natural subtraction would be wrong. -/
def select (mode : Mode) (lane : Lane) (b c : Nat) : Selection :=
  let offset := BitVec.ofNat 5 b
  let clamp := BitVec.ofNat 5 c
  let segment := BitVec.ofNat 5 (c / 256)
  let lower := lane &&& segment
  let bound := lower ||| (clamp &&& ~~~segment)
  match mode with
  | .up =>
      let index : Int := (lane.toNat : Int) - (offset.toNat : Int)
      if (bound.toNat : Int) ≤ index then ⟨BitVec.ofNat 5 index.toNat,true⟩ else ⟨lane,false⟩
  | .down =>
      let index := lane.toNat + offset.toNat
      if index ≤ bound.toNat then ⟨BitVec.ofNat 5 index,true⟩ else ⟨lane,false⟩
  | .bfly =>
      let index := lane ^^^ offset
      if index.toNat ≤ bound.toNat then ⟨index,true⟩ else ⟨lane,false⟩
  | .idx =>
      let index := lower ||| (offset &&& ~~~segment)
      if index.toNat ≤ bound.toNat then ⟨index,true⟩ else ⟨lane,false⟩

def member (mask : Nat) (lane : Lane) : Bool := mask.testBit lane.toNat
def linear (block : Dim3) (id : ThreadId) := id.tid.linear block
def lane (block : Dim3) (id : ThreadId) : Lane := BitVec.ofNat 5 (linear block id)
def SameWarp (block : Dim3) (left right : ThreadId) : Prop :=
  left.cta = right.cta ∧ linear block left / 32 = linear block right / 32

inductive Instr
  | scalar (instruction : Scalar.Instr)
  | shfl (mode : Mode) (dst : String) (predicate : Option String) (a b c mask : Ptx.Operand)

def InstructionTyped (registers : Scalar.RegisterDeclarations) (parameters : ParameterDeclarations) (length : Nat) : Instr → Prop
  | .scalar instruction => Scalar.InstructionTyped registers parameters length instruction
  | .shfl _ dst predicate a b c mask =>
      RegisterFits (Scalar.integerDeclarations registers) 32 dst ∧
      (∀ name ∈ predicate, RegisterFits (Scalar.integerDeclarations registers) 1 name) ∧
      OperandTyped (Scalar.integerDeclarations registers) 32 a ∧ OperandTyped (Scalar.integerDeclarations registers) 32 b ∧
      OperandTyped (Scalar.integerDeclarations registers) 32 c ∧ OperandTyped (Scalar.integerDeclarations registers) 32 mask
instance (registers parameters length instruction) : Decidable (InstructionTyped registers parameters length instruction) := by
  cases instruction <;> simp only [InstructionTyped] <;> infer_instance

def ProgramTyped (sm : Nat) (registers : Scalar.RegisterDeclarations) (parameters : ParameterDeclarations) (code : List Instr) : Prop :=
  70 ≤ sm ∧ (registers.map Prod.fst).Nodup ∧ (parameters.map Prod.fst).Nodup ∧
  (∀ parameter ∈ parameters, SupportedWidth parameter.2) ∧ code ≠ [] ∧
  ∀ instruction ∈ code, InstructionTyped registers parameters code.length instruction
instance (sm registers parameters code) : Decidable (ProgramTyped sm registers parameters code) := by
  unfold ProgramTyped; infer_instance
structure CheckedProgram where
  targetSM : Nat
  registers : Scalar.RegisterDeclarations
  parameters : ParameterDeclarations
  code : List Instr
  valid : ProgramTyped targetSM registers parameters code

theorem CheckedProgram.instruction_typed (program : CheckedProgram) {instruction} (hi : instruction ∈ program.code) :
    InstructionTyped program.registers program.parameters program.code.length instruction := program.valid.2.2.2.2.2 instruction hi

/-- Shuffle slots are intercepted before ordinary stepping. This list is only
a delegate fetch aid and is never an erasure certificate for shuffle semantics. -/
def scalarSkeleton (code : List Instr) : List Scalar.Instr := code.map (fun instruction => match instruction with
  | .scalar instruction => instruction
  | .shfl .. => .integer .ret)

theorem scalarSkeleton_slot {code : List Instr} {pc : Nat} {instruction : Scalar.Instr} (hi : code[pc]? = some (.scalar instruction)) :
    (scalarSkeleton code)[pc]? = some instruction := by simp only [scalarSkeleton,List.getElem?_map,hi,Option.map_some]

end
end Ptx.Shuffle
