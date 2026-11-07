import Ptx.ISA.Syntax

/-! Proof-carrying program data for the current strict integer frontend subset.
Type checking retains declaration types and validates every instruction, including
unreachable instructions. It is separate from register initialization, memory/UB
safety, progress, semantic PTX compliance and kernel functional correctness.
The strict equal-width rules intentionally cover less than PTX's relaxed ld/st
operand compatibility. New forms require explicit typing and execution rules.
-/
namespace Ptx.ISA

inductive RegisterType | u32 | s32 | u64 | b32 | b64 | pred deriving Repr, DecidableEq

def RegisterType.bits : RegisterType → Nat
  | .u32 | .s32 | .b32 => 32
  | .u64 | .b64 => 64
  | .pred => 1

abbrev RegisterDeclarations := List (String × RegisterType)
abbrev ParameterDeclarations := List (String × Nat)

def declarationLookup (name : String) : List (String × α) → Option α
  | [] => none
  | (key,value)::rest => if key == name then some value else declarationLookup name rest

def RegisterFits (registers : RegisterDeclarations) (width : Nat) (name : String) : Prop :=
  match declarationLookup name registers with
  | some .u32 | some .s32 | some .b32 => 32 = width
  | some .u64 | some .b64 => 64 = width
  | some .pred => 1 = width
  | none => False

instance (registers width name) : Decidable (RegisterFits registers width name) := by
  unfold RegisterFits
  split <;> infer_instance

theorem register_fits_bits {registers width name ty}
    (hf : RegisterFits registers width name) (hd : declarationLookup name registers = some ty) : ty.bits = width := by
  cases ty <;> simpa only [RegisterFits,hd,RegisterType.bits] using hf

def SupportedWidth (width : Nat) : Prop := width = 32 ∨ width = 64
instance (width) : Decidable (SupportedWidth width) := inferInstanceAs (Decidable (width = 32 ∨ width = 64))

def OperandTyped (registers : RegisterDeclarations) (width : Nat) : Operand → Prop
  | .imm value => value < 2^width
  | .reg name => RegisterFits registers width name
  | .tid => width = 32

instance (registers width operand) : Decidable (OperandTyped registers width operand) := by
  cases operand <;> simp only [OperandTyped] <;> infer_instance

def AddressTyped (registers : RegisterDeclarations) (address : Address) : Prop :=
  OperandTyped registers 64 address.base ∧ address.offset < 2^64
instance (registers address) : Decidable (AddressTyped registers address) :=
  inferInstanceAs (Decidable (OperandTyped registers 64 address.base ∧ address.offset < 2^64))

def BinaryForm (op : BinOp) (input output : Nat) : Prop :=
  SupportedWidth input ∧ (output = input ∨ (op = .mul ∧ input = 32 ∧ output = 64))
instance (op input output) : Decidable (BinaryForm op input output) :=
  inferInstanceAs (Decidable (SupportedWidth input ∧ (output = input ∨ (op = .mul ∧ input = 32 ∧ output = 64))))

/-- PTX shift counts are u32 even when the shifted value is u64. -/
def binaryRightWidth (op : BinOp) (input : Nat) : Nat := if op = .shr then 32 else input

def InstructionTyped (registers : RegisterDeclarations) (parameters : ParameterDeclarations) (length : Nat) : Instr → Prop
  | .mov width dst src => SupportedWidth width ∧ RegisterFits registers width dst ∧ OperandTyped registers width src
  | .param width dst name => SupportedWidth width ∧ RegisterFits registers width dst ∧
      declarationLookup name parameters = some width
  | .bin op input output dst a b => BinaryForm op input output ∧ RegisterFits registers output dst ∧
      OperandTyped registers input a ∧ OperandTyped registers (binaryRightWidth op input) b
  | .setp _ dst a b => RegisterFits registers 1 dst ∧ OperandTyped registers 32 a ∧ OperandTyped registers 32 b
  | .load _ dst address => RegisterFits registers 32 dst ∧ AddressTyped registers address
  | .store _ address value => AddressTyped registers address ∧ OperandTyped registers 32 value
  | .branch pred _ target => RegisterFits registers 1 pred ∧ target < length
  | .jump target => target < length
  | .barrier bid => bid < 16
  | .ret => True

instance (registers parameters length instruction) : Decidable (InstructionTyped registers parameters length instruction) := by
  cases instruction <;> simp only [InstructionTyped] <;> infer_instance

def ProgramTyped (registers : RegisterDeclarations) (parameters : ParameterDeclarations) (code : List Instr) : Prop :=
  (registers.map Prod.fst).Nodup ∧ (parameters.map Prod.fst).Nodup ∧
  (∀ p ∈ parameters, SupportedWidth p.2) ∧ code ≠ [] ∧
  ∀ instruction ∈ code, InstructionTyped registers parameters code.length instruction

instance (registers parameters code) : Decidable (ProgramTyped registers parameters code) := by
  unfold ProgramTyped
  infer_instance

abbrev TypedInstruction (registers : RegisterDeclarations) (parameters : ParameterDeclarations) (length : Nat) :=
  { instruction : Instr // InstructionTyped registers parameters length instruction }

structure CheckedProgram where
  registers : RegisterDeclarations
  parameters : ParameterDeclarations
  code : List Instr
  valid : ProgramTyped registers parameters code

def CheckedProgram.instructions (program : CheckedProgram) :
    List (TypedInstruction program.registers program.parameters program.code.length) :=
  program.code.attach.map (fun instruction => ⟨instruction.1,program.valid.2.2.2.2 instruction.1 instruction.2⟩)

theorem CheckedProgram.instruction_typed (program : CheckedProgram) {instruction : Instr} (hi : instruction ∈ program.code) :
    InstructionTyped program.registers program.parameters program.code.length instruction := program.valid.2.2.2.2 instruction hi

/-- Erasure preserves ALL instructions and their order; it cannot omit an
unreachable instruction or silently change the program used by existing proofs. -/
theorem CheckedProgram.instructions_erase (program : CheckedProgram) : program.instructions.map Subtype.val = program.code := by
  simp [instructions,List.map_map,Function.comp_def]

theorem CheckedProgram.register_names_unique (program : CheckedProgram) :
    (program.registers.map Prod.fst).Nodup := program.valid.1

end Ptx.ISA
