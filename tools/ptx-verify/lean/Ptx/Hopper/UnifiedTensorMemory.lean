import Ptx.Hopper.UnifiedCollective
import Ptx.Hopper.UnifiedVisibility

/-! Bridge actual representative operand reads to all lanes' tensor arithmetic.
The candidate/collective and RF are arbitrary. Input matrices are identified
by admitted byte reads and represented storage, not a desired matrix reply.
Arithmetic admission, source reconstruction and lifetime remain obligations.
-/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

theorem collective_input_from_sources {resolve descriptor candidate issue initial rf co histories cluster memory}
    (collective : Collective candidate issue)
    (hc : CausalConstraints resolve descriptor candidate initial rf co histories cluster)
    (writer : Wgmma.OperandByte → Node)
    (he : ∀ operand, Eligible resolve descriptor candidate histories cluster rf (.wgmmaRead issue operand)
      (Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand))
    (hs : ∀ operand, rf (.wgmmaRead issue operand) (Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand) = some (writer operand))
    (hw : ∀ operand, writeByte resolve descriptor candidate (writer operand)
      (Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand) =
      some (memory (Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand))) :
    Wgmma.InputAgreement issue.thread.cta (collective.calls 0) memory := by
  intro operand
  exact Option.some.inj ((write_read_value hc.agreement (he operand)
    (native_read_byte (collective_representative collective)) (hs operand)).symm.trans (hw operand))

theorem collective_arithmetic_inputs_identified {candidate issue memory a b}
    (collective : Collective candidate issue)
    (hi : Wgmma.InputAgreement issue.thread.cta (collective.calls 0) memory)
    (hm : Wgmma.MatrixStorage issue.thread.cta (collective.calls 0) memory a b)
    (ht : ∃ aa bb, (∀ lane, Wgmma.InputValues (collective.calls lane) aa bb) ∧
      Wgmma.Arithmetic aa bb (fun p => (collective.calls p.1).input p.2) (fun p => (collective.calls p.1).output p.2)) :
    (∀ lane, Wgmma.InputValues (collective.calls lane) a b) ∧
      Wgmma.Arithmetic a b (fun p => (collective.calls p.1).input p.2) (fun p => (collective.calls p.1).output p.2) := by
  obtain ⟨aa,bb,hv,ha⟩ := ht
  obtain ⟨rfl,rfl⟩ := Wgmma.input_values_unique (hv 0) (Wgmma.input_values_of_memory hi hm)
  exact ⟨hv,ha⟩

theorem collective_tensor_from_representative {candidate issue memory a b}
    (collective : Collective candidate issue)
    (ha : Wgmma.MatrixDescriptor.Packed (collective.calls 0).a)
    (hb : Wgmma.MatrixDescriptor.Packed (collective.calls 0).b)
    (hi : Wgmma.InputAgreement issue.thread.cta (collective.calls 0) memory)
    (hm : Wgmma.MatrixStorage issue.thread.cta (collective.calls 0) memory a b)
    (ht : ∃ aa bb, (∀ lane, Wgmma.InputValues (collective.calls lane) aa bb) ∧
      Wgmma.Arithmetic aa bb (fun p => (collective.calls p.1).input p.2) (fun p => (collective.calls p.1).output p.2)) :
    Wgmma.TensorConditions issue.thread.cta collective.calls memory := by
  obtain ⟨hv,harith⟩ := collective_arithmetic_inputs_identified collective hi hm ht
  refine ⟨collective.cohort,ha,hb,?_,a,b,hv,harith⟩
  intro lane operand
  have hl : Wgmma.operandLocation issue.thread.cta (collective.calls lane) operand =
      Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand := by
    cases operand <;> simp only [Wgmma.operandLocation,collective.cohort.a,collective.cohort.b]
  rw [hl]
  cases operand with
  | a p byte => exact ((hv lane).1 p byte).trans ((hv 0).1 p byte).symm |>.trans (hi (.a p byte))
  | b p byte => exact ((hv lane).2 p byte).trans ((hv 0).2 p byte).symm |>.trans (hi (.b p byte))

theorem collective_tensor_from_memory {resolve descriptor candidate issue initial rf co histories cluster memory a b}
    (collective : Collective candidate issue)
    (hc : CausalConstraints resolve descriptor candidate initial rf co histories cluster)
    (writer : Wgmma.OperandByte → Node)
    (he : ∀ operand, Eligible resolve descriptor candidate histories cluster rf (.wgmmaRead issue operand)
      (Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand))
    (hs : ∀ operand, rf (.wgmmaRead issue operand) (Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand) = some (writer operand))
    (hw : ∀ operand, writeByte resolve descriptor candidate (writer operand)
      (Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand) =
      some (memory (Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand)))
    (ha : Wgmma.MatrixDescriptor.Packed (collective.calls 0).a)
    (hb : Wgmma.MatrixDescriptor.Packed (collective.calls 0).b)
    (hm : Wgmma.MatrixStorage issue.thread.cta (collective.calls 0) memory a b)
    (ht : ∃ aa bb, (∀ lane, Wgmma.InputValues (collective.calls lane) aa bb) ∧
      Wgmma.Arithmetic aa bb (fun p => (collective.calls p.1).input p.2) (fun p => (collective.calls p.1).output p.2)) :
    Wgmma.TensorConditions issue.thread.cta collective.calls memory :=
  collective_tensor_from_representative collective ha hb (collective_input_from_sources collective hc writer he hs hw) hm ht

theorem collective_arithmetic_result_from_memory {resolve descriptor candidate issue initial rf co histories cluster memory a b c}
    (collective : Collective candidate issue)
    (hc : CausalConstraints resolve descriptor candidate initial rf co histories cluster)
    (writer : Wgmma.OperandByte → Node)
    (he : ∀ operand, Eligible resolve descriptor candidate histories cluster rf (.wgmmaRead issue operand)
      (Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand))
    (hs : ∀ operand, rf (.wgmmaRead issue operand) (Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand) = some (writer operand))
    (hw : ∀ operand, writeByte resolve descriptor candidate (writer operand)
      (Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand) =
      some (memory (Wgmma.operandLocation issue.thread.cta (collective.calls 0) operand)))
    (hm : Wgmma.MatrixStorage issue.thread.cta (collective.calls 0) memory a b)
    (ht : ∃ aa bb, (∀ lane, Wgmma.InputValues (collective.calls lane) aa bb) ∧
      Wgmma.Arithmetic aa bb (fun p => (collective.calls p.1).input p.2) (fun p => (collective.calls p.1).output p.2))
    (hin : ∀ p, (collective.calls p.1).input p.2 = Wgmma.gatherC c p) :
    Wgmma.scatterC (fun p => (collective.calls p.1).output p.2) = Wgmma.matrixStep a b c := by
  have ha := (collective_arithmetic_inputs_identified collective
    (collective_input_from_sources collective hc writer he hs hw) hm ht).2
  have hout : (fun p => (collective.calls p.1).output p.2) =
      Wgmma.results a b (fun p => (collective.calls p.1).input p.2) := funext ha
  rw [hout,funext hin]
  simp only [Wgmma.results,Wgmma.scatter_gather_c]

end
end Ptx.Hopper.Unified
