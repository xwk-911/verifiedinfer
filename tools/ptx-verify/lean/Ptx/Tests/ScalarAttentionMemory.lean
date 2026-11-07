import Ptx.Kernels.ScalarAttentionWitness
import Mathlib.Tactic.NormNum

/-! Multi-CTA arbitrary-candidate output/frame checks, a separate complete global
witness, inconsistent reads/output/frame rejection, and N=0 with unused invalid
scale memory and aliased matrices/output. All results use the exact-real model. -/
namespace Ptx.ScalarAttentionMemoryTests
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarAttention Ptx.ScalarAttentionEvent
noncomputable section

def input : Inputs := {
  q := 0, key := 64, value := 128, scale := 192, output := 256, m := 3, n := 2, dim := 3
  q64 := by decide, key64 := by decide, value64 := by decide, scale64 := by decide, output64 := by decide
  m32 := by decide, n32 := by decide, dim32 := by decide
}
def geometry : Geometry := ⟨⟨2,2,1⟩,⟨2,2,1⟩⟩
def cfg : Config := {
  input := input, geometry := geometry
  valid := by norm_num [geometry,Geometry.Valid,Dim3.Positive]
  gridZ := rfl, blockZ := rfl
  gridX32 := by decide, gridY32 := by decide, blockX32 := by decide, blockY32 := by decide
  extentX32 := by decide, extentY32 := by decide
  coversRows := by decide, coversCols := by decide
  outputEnd := by decide, outputAligned := by intros; decide
  readLayout := by
    intro _
    constructor <;> (first | decide | (unfold WordsDisjoint; decide))
}
def q : Attention.Matrix := fun _ _ => 1
def key : Attention.Matrix := fun _ _ => 0
def value : Attention.Matrix := fun _ _ => 7
def initial (loc : Location) : Symbolic.Byte :=
  if loc.space = .global ∧ loc.address < 36 then .realPart .f32 1 (loc.address%4)
  else if loc.space = .global ∧ 64 ≤ loc.address ∧ loc.address < 88 then .realPart .f32 0 ((loc.address-64)%4)
  else if loc.space = .global ∧ 128 ≤ loc.address ∧ loc.address < 152 then .realPart .f32 7 ((loc.address-128)%4)
  else if loc.space = .global ∧ 192 ≤ loc.address ∧ loc.address < 196 then .realPart .f32 1 ((loc.address-192)%4)
  else .bits (byte 165)
def launch : Scalar.Launch :=
  ⟨geometry,[("Q",0),("K",64),("V",128),("O",256),("Scale",192),("M",3),("N",2),("D",3)],initial⟩
def domain : List Location := (List.range 512).map (fun address => ⟨.global,address⟩)

theorem initialized : Initialized cfg q key value 1 initial := by
  intro _
  constructor
  · intro offset ho
    change offset < 4 at ho
    change initial ⟨.global,192+offset⟩ = .realPart .f32 1 offset
    have h0 : ¬ 192+offset < 36 := by omega
    have h1 : ¬ 192+offset < 88 := by omega
    have h2 : ¬ 192+offset < 152 := by omega
    have h3 : 192+offset < 196 := by omega
    simp [initial,h0,h1,h2,h3,ho,Nat.mod_eq_of_lt ho]
  constructor
  · intro r k hr hk offset ho
    change r < 3 at hr
    change k < 3 at hk
    change offset < 4 at ho
    change initial ⟨.global,0+4*(r*3+k)+offset⟩ = .realPart .f32 1 offset
    have hh : 4*(r*3+k)+offset < 36 := by omega
    have hm : (4*(r*3+k)+offset)%4 = offset := by omega
    simp [initial,hh,hm]
  constructor
  · intro j k hj hk offset ho
    change j < 2 at hj
    change k < 3 at hk
    change offset < 4 at ho
    change initial ⟨.global,64+4*(j*3+k)+offset⟩ = .realPart .f32 0 offset
    have h0 : ¬ 64+4*(j*3+k)+offset < 36 := by omega
    have hlo : 64 ≤ 64+4*(j*3+k)+offset := by omega
    have hhi : 64+4*(j*3+k)+offset < 88 := by omega
    have hm : (64+4*(j*3+k)+offset-64)%4 = offset := by omega
    simp [initial,h0,hlo,hhi,hm]
  · intro j c hj hc offset ho
    change j < 2 at hj
    change c < 3 at hc
    change offset < 4 at ho
    change initial ⟨.global,128+4*(j*3+c)+offset⟩ = .realPart .f32 7 offset
    have h0 : ¬ 128+4*(j*3+c)+offset < 36 := by omega
    have h1 : ¬ 128+4*(j*3+c)+offset < 88 := by omega
    have hlo : 128 ≤ 128+4*(j*3+c)+offset := by omega
    have hhi : 128+4*(j*3+c)+offset < 152 := by omega
    have hm : (128+4*(j*3+c)+offset-128)%4 = offset := by omega
    simp [initial,h0,h1,hlo,hhi,hm]

theorem pre : Pre cfg q key value 1 launch := by
  refine ⟨rfl,?_,initialized⟩
  constructor <;> rfl

theorem covers : CoversOutput cfg domain := by
  intro r c hr hc offset ho
  change r < 3 at hr
  change c < 3 at hc
  apply List.mem_map.mpr
  exact ⟨256+4*(r*3+c)+offset,List.mem_range.mpr (by omega),rfl⟩

theorem contract : Scalar.Triple code (Pre cfg q key value 1) (fun _ => domain)
    (fun launch output => Attention.Post q key value (Real.log 2*1) cfg.input.m cfg.input.n cfg.input.dim cfg.input.output output ∧
      ∀ loc ∈ domain, ¬ InWords cfg.input.output (cfg.input.m*cfg.input.dim) loc → output loc = launch.initial loc) :=
  correct cfg q key value 1 domain covers

theorem observed_cell {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    readReal .f32 o.output (outputLoc cfg 0 0) = some 7 := by
  have hresult := Scalar.triple_apply contract pre hw hm ho hd
  have hread := represents_read (hresult.1 0 0 (by decide) (by decide))
  norm_num [cfg,input,q,key,value,Attention.output,Attention.numerator,Attention.denominator,
    Attention.score,Attention.dot,Finset.sum_range_succ] at hread
  exact hread

theorem observed_frame {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    o.output ⟨.global,500⟩ = .bits (byte 165) := by
  have hmem : (⟨.global,500⟩ : Location) ∈ o.domain := by rw [hd]; simp [domain]
  have hout : ¬ InWords cfg.input.output (cfg.input.m*cfg.input.dim) ⟨.global,500⟩ := by
    norm_num [InWords,cfg,input]
  have h := frame hw pre.1 pre.2.1 ho hmem hout
  simpa [launch,initial] using h

theorem wrong_output_rejected {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (hm : GenericMemoryConditions execution initial rf co)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    readReal .f32 o.output (outputLoc cfg 0 0) ≠ some 8 := by
  rw [observed_cell hw hm ho hd]
  norm_num

theorem zeroed_frame_rejected {execution : Scalar.Candidate} {rf co o}
    (hw : Scalar.WellFormed code launch execution)
    (ho : ObserverConditions execution initial rf co o) (hd : o.domain = domain) :
    o.output ⟨.global,500⟩ ≠ .bits (byte 0) := by
  rw [observed_frame hw ho hd]
  intro he
  exact (show byte 165 ≠ byte 0 by decide) (Symbolic.Byte.bits.inj he)

theorem repeated_q_disagreement_rejected {execution : Scalar.Candidate} {rf co} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id)
    (hwrong : ScalarAttentionTrace.qValues (layout cfg launch.params t.id ha (by decide)) t.oracle 0 0 ≠
      ScalarAttentionTrace.qValues (layout cfg launch.params t.id ha (by decide)) t.oracle 1 0) :
    ¬ GenericMemoryConditions execution initial rf co := by
  intro hm
  have h0 := q_read_value hw hd pre.1 pre.2.1 initialized hm ht ha (by decide) (j := 0) (k := 0) (by decide) (by decide)
  have h1 := q_read_value hw hd pre.1 pre.2.1 initialized hm ht ha (by decide) (j := 1) (k := 0) (by decide) (by decide)
  exact hwrong (h0.trans h1.symm)

theorem wrong_scale_rejected {execution : Scalar.Candidate} {rf co} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (hwrong : replyReal t.oracle 0 = 17) :
    ¬ GenericMemoryConditions execution initial rf co := by
  intro hm
  have h := scale_read_value hw hd pre.1 pre.2.1 initialized hm ht ha (by decide)
  norm_num [hwrong] at h

theorem domain_global : ∀ loc ∈ domain, loc.space = .global := by
  intro loc hm
  obtain ⟨address,_,rfl⟩ := List.mem_map.mp hm
  rfl

theorem legal_execution : ∃ execution rf co o,
    Scalar.WellFormed code launch execution ∧ GenericMemoryConditions execution initial rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain :=
  nonvacuous cfg q key value 1 domain domain_global launch pre

theorem legal_execution_observes_seven : ∃ execution rf co o,
    Scalar.WellFormed code launch execution ∧ GenericMemoryConditions execution initial rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain ∧
    readReal .f32 o.output (outputLoc cfg 0 0) = some 7 ∧ o.output ⟨.global,500⟩ = .bits (byte 165) := by
  obtain ⟨execution,rf,co,o,hw,hm,ho,hd⟩ := legal_execution
  exact ⟨execution,rf,co,o,hw,hm,ho,hd,observed_cell hw hm ho hd,observed_frame hw ho hd⟩

def zeroInput : Inputs := {input with
  q := 256, key := 256, value := 256, scale := 2^64-1, n := 0
  q64 := by decide, key64 := by decide, value64 := by decide, scale64 := by decide, n32 := by decide}
def zeroCfg : Config := {cfg with
  input := zeroInput
  outputEnd := by decide, outputAligned := by intros; decide
  readLayout := by intro h; have hn : 0 < 0 := h.2.2; omega}
def zeroLaunch : Scalar.Launch :=
  ⟨geometry,[("Q",256),("K",256),("V",256),("O",256),("Scale",2^64-1),("M",3),("N",0),("D",3)],initial⟩

theorem zero_pre : Pre zeroCfg q key value 1 zeroLaunch := by
  refine ⟨rfl,?_,?_⟩
  · constructor <;> rfl
  · intro h
    have hn : 0 < 0 := h.2.2
    omega

theorem zero_covers : CoversOutput zeroCfg domain := by
  simpa only [CoversOutput,zeroCfg,zeroInput,cfg,input,outputLoc] using covers

theorem zero_unused_scale_invalid : zeroCfg.input.scale < 2^64 ∧
    ¬ zeroCfg.input.scale+4 ≤ 2^64 ∧ zeroCfg.input.scale % 4 ≠ 0 := by decide

theorem zero_keys_legal_output : ∃ execution rf co o,
    Scalar.WellFormed code zeroLaunch execution ∧ GenericMemoryConditions execution initial rf co ∧
    ObserverConditions execution initial rf co o ∧ o.domain = domain ∧
    readReal .f32 o.output (outputLoc zeroCfg 0 0) = some 0 := by
  obtain ⟨execution,rf,co,o,hw,hm,ho,hd⟩ := nonvacuous zeroCfg q key value 1 domain domain_global zeroLaunch zero_pre
  refine ⟨execution,rf,co,o,hw,hm,ho,hd,?_⟩
  have hc := Scalar.triple_apply (correct zeroCfg q key value 1 domain zero_covers) zero_pre hw hm ho hd
  exact represents_read (hc.1 0 0 (by decide) (by decide))

theorem read_start_does_not_bound_word : 2^64-3 < (2^64 : Nat) ∧ ¬ (2^64-3)+4 ≤ (2^64 : Nat) := by decide
theorem live_scale_output_overlap_rejected : ¬ WordsDisjoint 256 1 256 9 := by unfold WordsDisjoint; decide

end
end Ptx.ScalarAttentionMemoryTests
