import Ptx.Kernels.AmpereTiledCorrect
import Ptx.Tests.AmpereTiledMemory

/-! Nonuniform represented four-CTA input and parameterized correctness
instantiations. These input/specification instances do not replace an independent
checked source/rf/co/observer witness, which remains a separate obligation. -/
namespace Ptx.AmpereTiledCorrectTests
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph Ptx.AmpereTiledPhaseTests
noncomputable section

def left (r k : Nat) : ℝ := 100*r+k
def right (k c : Nat) : ℝ := 1000*k+c
def initial (loc : Location) : Symbolic.Byte :=
  if loc.space = .global ∧ 128 ≤ loc.address ∧ loc.address < 3200 then
    .realPart .f16 (left (((loc.address-128)/2)/48) (((loc.address-128)/2)%48)) ((loc.address-128)%2)
  else if loc.space = .global ∧ 8192 ≤ loc.address ∧ loc.address < 9728 then
    .realPart .f16 (right (((loc.address-8192)/2)%48) (((loc.address-8192)/2)/48)) ((loc.address-8192)%2)
  else .bits (byte 165)
def representedLaunch : Scalar.Launch := {launch with initial := initial}

theorem represented_input : Input input left right initial := by
  intro _
  constructor
  · intro row k hr hk offset ho
    change row < 32 at hr
    change k < 48 at hk
    change offset < 2 at ho
    change initial (⟨.global,128+2*(row*48+k)+offset⟩ : Location) = .realPart .f16 (left row k) offset
    have hrange : 128 ≤ 128+2*(row*48+k)+offset ∧ 128+2*(row*48+k)+offset < 3200 := by omega
    have hrow : ((128+2*(row*48+k)+offset-128)/2)/48 = row := by omega
    have hcol : ((128+2*(row*48+k)+offset-128)/2)%48 = k := by omega
    have hoff : (128+2*(row*48+k)+offset-128)%2 = offset := by omega
    simp [initial,hrange.1,hrange.2,hrow,hcol,hoff]
  · intro k col hk hc offset ho
    change k < 48 at hk
    change col < 16 at hc
    change offset < 2 at ho
    change initial (⟨.global,8192+2*(col*48+k)+offset⟩ : Location) = .realPart .f16 (right k col) offset
    have hnot : ¬ (128 ≤ 8192+2*(col*48+k)+offset ∧ 8192+2*(col*48+k)+offset < 3200) := by omega
    have hrange : 8192 ≤ 8192+2*(col*48+k)+offset ∧ 8192+2*(col*48+k)+offset < 9728 := by omega
    have hrow : ((8192+2*(col*48+k)+offset-8192)/2)/48 = col := by omega
    have hcol : ((8192+2*(col*48+k)+offset-8192)/2)%48 = k := by omega
    have hoff : (8192+2*(col*48+k)+offset-8192)%2 = offset := by omega
    simp [initial,hnot,hrange.1,hrange.2,hrow,hcol,hoff]

theorem represented_pre : Pre input left right representedLaunch :=
  ⟨AmpereTiledSourceTests.layout,represented_input,rfl,rfl⟩
theorem universal_contract : CheckedTriple AmpereTiledGraph.code (Pre input left right) (fun _ => domain input)
    (fun l output => Post input left right l.initial output) := AmpereTiledCorrect.correct input left right

theorem a_upper_last_pair : AmpereTiledInputRead.expected left right reader 2 3 0 = 3146 ∧
    AmpereTiledInputRead.expected left right reader 2 3 1 = 3147 := by norm_num [AmpereTiledInputRead.expected,AmpereTiledInputRead.inputRow,AmpereTiledInputRead.inputK,reader,left]
theorem b_column_major_last_pair : AmpereTiledInputRead.expected left right reader 2 5 0 = 46015 ∧
    AmpereTiledInputRead.expected left right reader 2 5 1 = 47015 := by norm_num [AmpereTiledInputRead.expected,AmpereTiledInputRead.inputCol,AmpereTiledInputRead.inputK,reader,right]
theorem actual_a_last_address : AmpereTiledProducer.inputBase input reader 2 3 = ⟨.global,3196⟩ := rfl
theorem actual_b_last_address : AmpereTiledProducer.inputBase input reader 2 5 = ⟨.global,9724⟩ := rfl
theorem first_read_producer : AmpereTiledProducer.producer reader 0 = writer := rfl
theorem upper_last_read_producer : AmpereTiledProducer.producer reader 3 = reader ∧ AmpereTiledProducer.part 3 = 1 := by decide
theorem last_b_read_producer : AmpereTiledProducer.producer reader 5 = reader ∧ AmpereTiledProducer.part 5 = 2 := by decide

theorem empty_matrix_contract (a b : Matrix) : CheckedTriple AmpereTiledGraph.code
    (Pre AmpereTiledSourceTests.rowMasked a b) (fun _ => domain AmpereTiledSourceTests.rowMasked)
    (fun l output => Post AmpereTiledSourceTests.rowMasked a b l.initial output) :=
  AmpereTiledCorrect.correct _ a b
theorem zero_k_contract (a b : Matrix) : CheckedTriple AmpereTiledGraph.code
    (Pre AmpereTiledSourceTests.zeroK a b) (fun _ => domain AmpereTiledSourceTests.zeroK)
    (fun l output => Post AmpereTiledSourceTests.zeroK a b l.initial output) :=
  AmpereTiledCorrect.correct _ a b

theorem admitted_nonuniform_post {candidate rf co o}
    (hc : CheckedConditions AmpereTiledGraph.code representedLaunch candidate rf co)
    (ho : ObserverConstraints candidate representedLaunch.initial rf co o) (hd : o.domain = domain input) :
    Post input left right representedLaunch.initial o.output :=
  universal_contract representedLaunch candidate rf co o represented_pre hc ho hd

end
end Ptx.AmpereTiledCorrectTests
