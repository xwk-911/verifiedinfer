import Ptx.Scalar.Stream
import Ptx.Kernels.StreamEffects

/-! A generated literal/shared kernel publishes A=9, then actual generated
scalar matmul consumes A and an arbitrary real B. This exercises the general
stream rules and their independent nonvacuity construction. It is a composition
baseline, not the required routing/expert/combine MoE case. -/
namespace Ptx.StreamPipeline
open Ptx.ISA Ptx.Scalar.Stream
noncomputable section

def wordDomain (base : Nat) : List Location := (List.range 4).map (fun offset => ⟨.global,base+offset⟩)
theorem word_mem (base : Nat) {offset : Nat} (ho : offset < 4) :
    (⟨.global,base+offset⟩ : Location) ∈ wordDomain base :=
  List.mem_map.mpr ⟨offset,List.mem_range.mpr ho,rfl⟩
theorem word_global (base : Nat) : ∀ loc ∈ wordDomain base, loc.space = .global := by
  intro loc hm
  obtain ⟨offset,_,rfl⟩ := List.mem_map.mp hm
  rfl
theorem word_outside {base address : Nat} (h : address < base ∨ base+4 ≤ address) :
    (⟨.global,address⟩ : Location) ∉ wordDomain base := by
  intro hm
  obtain ⟨offset,ho,he⟩ := List.mem_map.mp hm
  have hoff := List.mem_range.mp ho
  have hh := congrArg Location.address he
  simp only at hh
  omega

def literal : Invocation := {
  code := FloatLiteralsTrace.code, geometry := ⟨.one,.one⟩,params := [("dst",64)]
  shared := fun _ _ => .bits (byte 17),domain := wordDomain 64
}
def input : ScalarMatmul.Inputs := {
  a := 64,b := 128,c := 192,m := 1,n := 1,k := 1
  a64 := by decide,b64 := by decide,c64 := by decide
  m32 := by decide,n32 := by decide,k32 := by decide
}
def cfg : ScalarMatmulEvent.Config := {
  input := input,geometry := ⟨.one,.one⟩
  valid := by simp [Geometry.Valid,Dim3.Positive,Dim3.one]
  gridZ := rfl,blockZ := rfl
  gridX32 := by decide,gridY32 := by decide,blockX32 := by decide,blockY32 := by decide
  extentX32 := by decide,extentY32 := by decide,coversRows := by decide,coversCols := by decide
  aEnd := by decide,bEnd := by decide,cEnd := by decide
  aAligned := by decide,bAligned := by decide,cAligned := by decide
  separateA := by decide,separateB := by decide
}
def matmul : Invocation := {
  code := ScalarMatmul.code,geometry := cfg.geometry
  params := [("A",64),("B",128),("C",192),("M",1),("N",1),("K",1)]
  shared := fun _ _ => .bits (byte 23),domain := wordDomain 192
}

def Pre (b : ℝ) (heap : Heap) : Prop := Represents .f32 heap 128 b
def Mid (b : ℝ) (before after : Heap) : Prop :=
  Represents .f32 after 64 9 ∧ Represents .f32 after 128 b ∧ after 250 = before 250
def Ready (b : ℝ) (heap : Heap) : Prop := Represents .f32 heap 64 9 ∧ Represents .f32 heap 128 b
def Post (b : ℝ) (before after : Heap) : Prop := Represents .f32 after 192 (9*b) ∧ after 250 = before 250

theorem literal_pre (heap : Heap) : FloatLiteralsUniversal.Pre 64 (literal.launch heap) := ⟨by decide,rfl,rfl⟩

theorem matmul_pre (b : ℝ) (heap : Heap) (hp : Ready b heap) :
    ScalarMatmulEvent.Pre cfg (fun _ _ => 9) (fun _ _ => b) (matmul.launch heap) := by
  refine ⟨rfl,?_,?_,?_⟩
  · constructor <;> rfl
  · intro r k hr hk
    have hr0 : r = 0 := by change r < 1 at hr; omega
    have hk0 : k = 0 := by change k < 1 at hk; omega
    subst r; subst k
    exact hp.1
  · intro k c hk hc
    have hk0 : k = 0 := by change k < 1 at hk; omega
    have hc0 : c = 0 := by change c < 1 at hc; omega
    subst k; subst c
    exact hp.2

theorem matmul_covers : ScalarMatmulEvent.CoversOutput cfg matmul.domain := by
  intro r c hr hc offset ho
  have hr0 : r = 0 := by change r < 1 at hr; omega
  have hc0 : c = 0 := by change c < 1 at hc; omega
  subst r; subst c
  exact word_mem 192 ho

theorem literal_correct (b : ℝ) : Scalar.Stream.Triple [literal] (Pre b) (Mid b) := by
  refine single_correct (pre := Pre b) (post := Mid b) literal
    (FloatLiteralsUniversal.checked_correct 64) (fun heap _ => literal_pre heap) ?_
  intro heap o hp hd hpost
  refine ⟨?_,?_,?_⟩
  · apply publish_represents (Scalar.read_represents hpost)
    intro offset ho
    rw [hd]
    exact word_mem 64 ho
  · intro offset ho
    rw [publish_outside (by rw [hd]; exact word_outside (.inr (by omega)))]
    exact hp offset ho
  · apply publish_outside
    rw [hd]
    exact word_outside (.inr (by decide))

theorem literal_nonvacuous (b : ℝ) : Scalar.Stream.Nonvacuous [literal] (Pre b) := by
  apply single_nonvacuous literal (FloatLiteralsUniversal.checked_nonvacuous 64) (fun heap _ => literal_pre heap)
  intro heap c rf co o _ hc ho _
  exact FloatLiteralsUniversal.covers_global_writes (literal_pre heap) hc.provenance ho.complete

theorem matmul_correct (b : ℝ) : Scalar.Stream.Triple [matmul] (Ready b) (Post b) := by
  refine single_correct (pre := Ready b) (post := Post b) matmul
    (ScalarMatmulEvent.checked_correct cfg (fun _ _ => 9) (fun _ _ => b) matmul.domain matmul_covers) (matmul_pre b) ?_
  intro heap o hp hd hpost
  constructor
  · have hr := hpost.1 0 0 (by decide) (by decide)
    have hrepr : Scalar.RepresentsReal .f32 o.output ⟨.global,192⟩ (9*b) := by
      simpa only [cfg,input,ScalarMatmul.prefixProduct,mul_one,add_zero,Nat.zero_mul,Nat.zero_add,Nat.mul_zero,Nat.add_zero] using hr
    apply publish_represents hrepr
    intro offset ho
    rw [hd]
    exact word_mem 192 ho
  · apply publish_outside
    rw [hd]
    exact word_outside (.inr (by decide))

theorem matmul_nonvacuous (b : ℝ) : Scalar.Stream.Nonvacuous [matmul] (Ready b) := by
  apply single_nonvacuous matmul
    (ScalarMatmulEvent.checked_nonvacuous cfg (fun _ _ => 9) (fun _ _ => b) matmul.domain (word_global 192)) (matmul_pre b)
  intro heap c rf co o hp hc ho _
  exact ScalarMatmulEvent.covers_global_writes hc.provenance ho.complete rfl (matmul_pre b heap hp).2.1 matmul_covers

theorem correct (b : ℝ) : Scalar.Stream.Triple [literal,matmul] (Pre b) (Post b) := by
  refine triple_append (first := [literal]) (rest := [matmul]) (pre := Pre b) (mid := Mid b) (post := Post b) (literal_correct b) ?_
  intro before hp
  refine triple_consequence (pre' := Mid b before) (post' := fun _ after => Post b before after) (matmul_correct b) ?_ ?_
  · intro mid hm; exact ⟨hm.1,hm.2.1⟩
  · intro mid after hm hpost
    exact ⟨hpost.1,hpost.2.trans hm.2.2⟩

theorem nonvacuous (b : ℝ) : Scalar.Stream.Nonvacuous [literal,matmul] (Pre b) := by
  apply nonvacuous_append (first := [literal]) (rest := [matmul]) (literal_nonvacuous b) (literal_correct b)
  intro before hp mid hm
  exact matmul_nonvacuous b mid ⟨hm.1,hm.2.1⟩

end
end Ptx.StreamPipeline
