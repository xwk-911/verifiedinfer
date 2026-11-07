import Ptx.Kernels.ScalarMatmulSpec
import Ptx.Scalar.Rules
import Mathlib.Tactic.NormNum

/-! Concrete source-execution evidence, separate from the outstanding arbitrary-K
loop invariant, launch-wide correctness and non-vacuity proofs. -/
namespace Ptx.ScalarMatmulTests
open Ptx.ISA Ptx.Scalar
noncomputable section

theorem generated_types : Scalar.ProgramTyped Generated.scalar_matmul.registerDeclarations
    Generated.scalar_matmul.parameters Generated.scalar_matmul.program := Generated.scalar_matmul.checked.valid

def ctx : Scalar.Context := {
  id := ⟨.zero,⟨1,1,0⟩⟩
  block := ⟨2,2,1⟩
  params := [("A",0),("B",64),("C",128),("M",2),("N",3),("K",0)]
}
def literalZero : ℝ := (F32Literal.mk 0 (by decide) (by decide)).value
def zeroFinal : Scalar.State := {
  core := {thread := {pc := 42,status := .done,regs := [
    ("%p",1),("%k",0),("%cp",144),("%stride",12),("%bp",68),("%offset",4),("%ap",0),
    ("%col",1),("%tx",1),("%sx",2),("%bx",0),("%row",1),("%ty",1),("%sy",2),("%by",0),
    ("%kmax",0),("%n",3),("%m",2),("%c",128),("%b",64),("%a",0)]}}
  floats := [("%acc",(.f32,literalZero))]
}

theorem literal_zero : literalZero = 0 := by norm_num [literalZero,F32Literal.value]

/-- The actual generated code skips both matrix loads for K=0, independently of
every oracle reply; the output address is C[1,1] for row-major N=3. -/
theorem zero_k_trace (oracle : Scalar.Oracle) :
    Scalar.run ctx oracle Generated.scalar_matmul.program 36 {} =
      .ok (zeroFinal,[.write ⟨.global,144⟩ (Symbolic.encode .f32 literalZero)]) := by rfl

theorem zero_k_output (oracle : Scalar.Oracle) :
    ∃ final, Scalar.run ctx oracle Generated.scalar_matmul.program 36 {} =
      .ok (final,[.write ⟨.global,144⟩ (Symbolic.encode .f32 0)]) ∧
      final.core.thread.status = .done ∧ final.core.queries = 0 := by
  refine ⟨zeroFinal,?_,rfl,rfl⟩
  simpa only [literal_zero] using zero_k_trace oracle

def twoContext : Scalar.Context := {
  ctx with params := [("A",0),("B",64),("C",128),("M",2),("N",3),("K",2)]
}
def twoOracle : Scalar.Oracle := fun query => .real .f32
  (if query = 0 then 2 else if query = 1 then 3 else if query = 2 then 5 else 7)
def twoAnswer : ℝ := 5*7+(2*3+literalZero)
def twoFinal : Scalar.State := {
  core := {queries := 4,thread := {pc := 42,status := .done,regs := [
    ("%p",1),("%k",2),("%bp",92),("%ap",16),("%cp",144),("%stride",12),("%offset",4),
    ("%col",1),("%tx",1),("%sx",2),("%bx",0),("%row",1),("%ty",1),("%sy",2),("%by",0),
    ("%kmax",2),("%n",3),("%m",2),("%c",128),("%b",64),("%a",0)]}}
  floats := [("%acc",(.f32,twoAnswer)),("%bv",(.f32,7)),("%av",(.f32,5))]
}

set_option maxRecDepth 4000 in
theorem two_k_trace : Scalar.run twoContext twoOracle Generated.scalar_matmul.program 54 {} =
    .ok (twoFinal,[.read ⟨.global,8⟩ (Symbolic.encode .f32 2),
      .read ⟨.global,68⟩ (Symbolic.encode .f32 3),.read ⟨.global,12⟩ (Symbolic.encode .f32 5),
      .read ⟨.global,80⟩ (Symbolic.encode .f32 7),.write ⟨.global,144⟩ (Symbolic.encode .f32 twoAnswer)]) := rfl

theorem two_k_output : twoFinal.core.thread.status = .done ∧ twoAnswer = 41 := by
  constructor
  · rfl
  · norm_num [twoAnswer,literal_zero]

end
end Ptx.ScalarMatmulTests
