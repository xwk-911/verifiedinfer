import Ptx.ISA.Fragments
import Ptx.ISA.Typing
import Ptx.Scalar.Context

namespace Ptx.Scalar
open Ptx.ISA
noncomputable section

/-- Exact finite f32 hexadecimal input literal. The bits are decoded ONLY at the
source-literal boundary, never by reinterpreting a symbolic in-memory float. -/
structure F32Literal where
  bits : Nat
  bounded : bits < 2^32
  finite : (bits / 2^23) % 256 < 255

def F32Literal.value (literal : F32Literal) : ℝ :=
  let exponent := (literal.bits / 8388608) % 256
  let fraction := literal.bits % 8388608
  let mantissa := if exponent = 0 then fraction else 8388608+fraction
  let power : Int := if exponent = 0 then -149 else (exponent : Int)-150
  let sign : ℝ := if literal.bits / 2147483648 = 0 then 1 else -1
  sign * (mantissa : ℝ) * (2 : ℝ)^power

@[simp] theorem F32Literal.zero_value : (F32Literal.mk 0 (by decide) (by decide)).value = 0 := by
  simp [F32Literal.value]

inductive FloatOperand
  | reg (name : String)
  | literal (value : F32Literal)

/-- Explicit scalar extension. Integer instructions keep their previous meaning;
floating operations are exact REAL operations, not IEEE rounded executions.
Arithmetic has exact real values; `ex2.approx.f32` is abstracted by exp(log 2 * x).
The accepted qualifiers are explicit constructors, not an IEEE implementation. -/
inductive Instr
  | integer (instruction : Ptx.Instr)
  | setpGt (format : Symbolic.Format) (dst : String) (a b : FloatOperand)
  | readSpecial (dst : String) (source : SpecialRegister)
  | atomAddU32 (dst : String) (address : Address) (increment : Ptx.Operand)
  | mov (format : Symbolic.Format) (dst : String) (src : FloatOperand)
  | addRn (format : Symbolic.Format) (dst : String) (a b : FloatOperand)
  | subRn (format : Symbolic.Format) (dst : String) (a b : FloatOperand)
  | mulRn (format : Symbolic.Format) (dst : String) (a b : FloatOperand)
  | divRn (format : Symbolic.Format) (dst : String) (a b : FloatOperand)
  | max (format : Symbolic.Format) (dst : String) (a b : FloatOperand)
  | ex2Approx (dst : String) (src : FloatOperand)
  | fmaRn (format : Symbolic.Format) (dst : String) (a b c : FloatOperand)
  | load (format : Symbolic.Format) (space : Ptx.Space) (dst : String) (address : Address)
  | store (format : Symbolic.Format) (space : Ptx.Space) (address : Address) (value : FloatOperand)

inductive RegisterType
  | integer (ty : ISA.RegisterType)
  | floating (format : Symbolic.Format)
  deriving Repr, DecidableEq

abbrev RegisterDeclarations := List (String × RegisterType)
def integerDeclarations (registers : RegisterDeclarations) : ISA.RegisterDeclarations :=
  registers.filterMap (fun (name,ty) => match ty with
    | .integer ty => some (name,ty)
    | .floating _ => none)

def FloatRegisterFits (registers : RegisterDeclarations) (format : Symbolic.Format) (name : String) : Prop :=
  match declarationLookup name registers with
  | some (.floating actual) => actual = format
  | some (.integer .b32) => format = .f32
  | some (.integer .b64) => format = .f64
  | _ => False
instance (registers format name) : Decidable (FloatRegisterFits registers format name) := by
  unfold FloatRegisterFits
  split <;> infer_instance

def FloatOperandTyped (registers : RegisterDeclarations) (format : Symbolic.Format) : FloatOperand → Prop
  | .reg name => FloatRegisterFits registers format name
  | .literal _ => format = .f32
instance (registers format operand) : Decidable (FloatOperandTyped registers format operand) := by
  cases operand <;> simp only [FloatOperandTyped] <;> infer_instance

def InstructionTyped (registers : RegisterDeclarations) (parameters : ParameterDeclarations) (length : Nat) : Instr → Prop
  | .integer i => ISA.InstructionTyped (integerDeclarations registers) parameters length i
  | .setpGt format dst a b => ISA.RegisterFits (integerDeclarations registers) 1 dst ∧
      FloatOperandTyped registers format a ∧ FloatOperandTyped registers format b
  | .readSpecial dst _ => ISA.RegisterFits (integerDeclarations registers) 32 dst
  | .atomAddU32 dst address increment => ISA.RegisterFits (integerDeclarations registers) 32 dst ∧
      AddressTyped (integerDeclarations registers) address ∧ OperandTyped (integerDeclarations registers) 32 increment
  | .mov format dst src => FloatRegisterFits registers format dst ∧ FloatOperandTyped registers format src
  | .addRn format dst a b | .subRn format dst a b | .mulRn format dst a b |
    .divRn format dst a b | .max format dst a b =>
      FloatRegisterFits registers format dst ∧ FloatOperandTyped registers format a ∧ FloatOperandTyped registers format b
  | .ex2Approx dst src => FloatRegisterFits registers .f32 dst ∧ FloatOperandTyped registers .f32 src
  | .fmaRn format dst a b c => FloatRegisterFits registers format dst ∧ FloatOperandTyped registers format a ∧
      FloatOperandTyped registers format b ∧ FloatOperandTyped registers format c
  | .load format _ dst address => FloatRegisterFits registers format dst ∧ AddressTyped (integerDeclarations registers) address
  | .store format _ address value => AddressTyped (integerDeclarations registers) address ∧ FloatOperandTyped registers format value
instance (registers parameters length instruction) : Decidable (InstructionTyped registers parameters length instruction) := by
  cases instruction <;> simp only [InstructionTyped] <;> infer_instance

def ProgramTyped (registers : RegisterDeclarations) (parameters : ParameterDeclarations) (code : List Instr) : Prop :=
  (registers.map Prod.fst).Nodup ∧ (parameters.map Prod.fst).Nodup ∧
  (∀ p ∈ parameters, ISA.SupportedWidth p.2) ∧ code ≠ [] ∧
  ∀ instruction ∈ code, InstructionTyped registers parameters code.length instruction
instance (registers parameters code) : Decidable (ProgramTyped registers parameters code) := by
  unfold ProgramTyped
  infer_instance

structure CheckedProgram where
  registers : RegisterDeclarations
  parameters : ParameterDeclarations
  code : List Instr
  valid : ProgramTyped registers parameters code

theorem CheckedProgram.instruction_typed (program : CheckedProgram) {instruction : Instr} (hi : instruction ∈ program.code) :
    InstructionTyped program.registers program.parameters program.code.length instruction := program.valid.2.2.2.2 instruction hi

end
end Ptx.Scalar
