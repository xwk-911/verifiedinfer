import Ptx.Kernels.ScalarAttentionAddress
import Ptx.Kernels.ScalarAttentionOuter

/-! Actual scale load and loop-entry address setup, PCs 30--36. Address
hypotheses bound read starts; global byte/allocation/race duties remain open. -/
namespace Ptx.ScalarAttentionInit
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttention
noncomputable section

structure AddressBounds (i : Inputs) (ctx : Scalar.Context) : Prop where
  output64 : outputAddress i ctx < 2^64
  qRead64 : ∀ k, k < i.dim → i.q+4*(row ctx.block ctx.id*i.dim)+4*k < 2^64
  keyRead64 : ∀ j k, j < i.n → k < i.dim → i.key+4*i.dim*j+4*k < 2^64
  valueRead64 : ∀ j, j < i.n → i.value+4*col ctx.block ctx.id+4*i.dim*j < 2^64

def threadLayout (i : Inputs) (ctx : Scalar.Context) (h : AddressBounds i ctx) : ScalarAttentionOuter.Layout := {
  keys := i.n, dim := i.dim, qBase := i.q+4*(row ctx.block ctx.id*i.dim)
  keyBase := i.key, valueBase := i.value+4*col ctx.block ctx.id, output := outputAddress i ctx, firstQuery := 1
  keys32 := i.n32, dim32 := i.dim32, output64 := h.output64
  qRead64 := h.qRead64, keyRead64 := h.keyRead64, valueRead64 := h.valueRead64
}

theorem loop_initialization (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {s : Scalar.State} (hi : Ready i ctx 30 s) (hb : IndexBounds ctx) (ha : AddressBounds i ctx)
    (scale : ℝ) (ho : oracle 0 = .real .f32 scale) (score value : Nat → ℝ) :
    ∃ next, Scalar.run ctx oracle code 7 s = .ok
      (next,[.read ⟨.global,i.scale⟩ (Symbolic.encode .f32 scale)]) ∧
      ScalarAttentionOuter.Inv (threadLayout i ctx ha) score value scale 0 next := by
  let r := row ctx.block ctx.id
  let c := col ctx.block ctx.id
  let s1 := loadedFloat s "%scale" scale
  let s2 := intAssign s1 "%qr" (wrap 64 (r*i.dim))
  let s3 := intAssign s2 "%qr" (wrap 64 ((r*i.dim)*4))
  let s4 := intAssign s3 "%qr" (wrap 64 (i.q+4*(r*i.dim)))
  let s5 := intAssign s4 "%vp" (wrap 64 (i.value+4*c))
  let s6 := intAssign s5 "%stride" (4*i.dim)
  let s7 := intAssign s6 "%j" 0
  have hrval : lookup "%row" s.core.thread.regs = some r := hi.rowValue
  have hr32 : wrap 32 r = r := Nat.mod_eq_of_lt hb.rowBound
  have hd32 : wrap 32 i.dim = i.dim := Nat.mod_eq_of_lt i.dim32
  have hQ64 : wrap 64 i.q = i.q := Nat.mod_eq_of_lt i.q64
  have hK64 : wrap 64 i.key = i.key := Nat.mod_eq_of_lt i.key64
  have hV64 : wrap 64 i.value = i.value := Nat.mod_eq_of_lt i.value64
  have hoff : wrap 64 (4*c) = 4*c := Nat.mod_eq_of_lt (by have := hb.colBound; change c < 2^32 at this; omega)
  have hstride : wrap 64 (4*i.dim) = 4*i.dim := Nat.mod_eq_of_lt (by have := i.dim32; omega)
  have hqeq : (r*i.dim)*4 = 4*(r*i.dim) := Nat.mul_comm _ _
  have hdeq : i.dim*4 = 4*i.dim := Nat.mul_comm _ _
  have h30 : Scalar.step ctx oracle code s = .ok
      (s1,[.read ⟨.global,i.scale⟩ (Symbolic.encode .f32 scale)]) := by
    apply load_step (format := .f32) (space := .global) (dst := "%scale")
      (address := {base := .reg "%sp"}) (addr := i.scale) (value := scale) hi.running (by rw [hi.pcValue]; rfl)
    · simp [evalAddr,Ptx.eval,hi.scale,show wrap 64 i.scale = i.scale from Nat.mod_eq_of_lt i.scale64,
        bind,Except.bind,pure,Except.pure]
    · simpa only [hi.queries] using ho
  have h31 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply integer_local_step (instruction := .bin .mul 32 64 "%qr" (.reg "%row") (.reg "%d"))
      (by simpa [s1,loadedFloat,writeFloat,advance] using hi.running)
      (by simp only [s1,loadedFloat,writeFloat,advance,hi.pcValue]; rfl)
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s1,hrval,hi.dim,hr32,hd32,bind,Except.bind,pure,Except.pure]
  have h32 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply integer_local_step (instruction := .bin .mul 64 64 "%qr" (.reg "%qr") (.imm 4))
      (by simpa [s2,s1,intAssign,finishInteger,assign,loadedFloat,writeFloat,advance] using hi.running)
      (by simp only [s2,s1,intAssign,finishInteger,assign,loadedFloat,writeFloat,advance,hi.pcValue]; rfl)
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s2,s1,wrap_mul,bind,Except.bind,pure,Except.pure]
  have h33 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply integer_local_step (instruction := .bin .add 64 64 "%qr" (.reg "%q") (.reg "%qr"))
      (by simpa [s3,s2,s1,intAssign,finishInteger,assign,loadedFloat,writeFloat,advance] using hi.running)
      (by simp only [s3,s2,s1,intAssign,finishInteger,assign,loadedFloat,writeFloat,advance,hi.pcValue]; rfl)
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s3,s2,s1,hi.q,hQ64,wrap_add_right,hqeq,bind,Except.bind,pure,Except.pure]
  have h34 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    apply integer_local_step (instruction := .bin .add 64 64 "%vp" (.reg "%vp") (.reg "%offset"))
      (by simpa [s4,s3,s2,s1,intAssign,finishInteger,assign,loadedFloat,writeFloat,advance] using hi.running)
      (by simp only [s4,s3,s2,s1,intAssign,finishInteger,assign,loadedFloat,writeFloat,advance,hi.pcValue]; rfl)
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s4,s3,s2,s1,hi.value,hi.offset,hV64,hoff,c,bind,Except.bind,pure,Except.pure]
  have h35 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    apply integer_local_step (instruction := .bin .mul 32 64 "%stride" (.reg "%d") (.imm 4))
      (by simpa [s5,s4,s3,s2,s1,intAssign,finishInteger,assign,loadedFloat,writeFloat,advance] using hi.running)
      (by simp only [s5,s4,s3,s2,s1,intAssign,finishInteger,assign,loadedFloat,writeFloat,advance,hi.pcValue]; rfl)
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s5,s4,s3,s2,s1,hi.dim,hd32,hdeq,hstride,show wrap 32 4 = 4 by decide,
      bind,Except.bind,pure,Except.pure]
  have h36 : Scalar.step ctx oracle code s6 = .ok (s7,[]) := by
    apply integer_local_step (instruction := .mov 32 "%j" (.imm 0))
      (by simpa [s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,loadedFloat,writeFloat,advance] using hi.running)
      (by simp only [s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,loadedFloat,writeFloat,advance,hi.pcValue]; rfl)
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,show wrap 32 0 = 0 by decide,bind,Except.bind,pure,Except.pure]
  have hrun : Scalar.run ctx oracle code 7 s = .ok
      (s7,[.read ⟨.global,i.scale⟩ (Symbolic.encode .f32 scale)]) := by
    simp [Scalar.run,h30,h31,h32,h33,h34,h35,h36,Except.bind]
  have hf : RegisterFrame ["%qr","%vp","%stride","%j"] s1 s7 := by
    apply register_frame_trans (intAssign_register_frame (loadedFloat_banks hi.banks _ _) "%qr" _ (by decide))
    apply register_frame_trans (intAssign_register_frame (intAssign_banks _ _ _) "%qr" _ (by decide))
    apply register_frame_trans (intAssign_register_frame (intAssign_banks _ _ _) "%qr" _ (by decide))
    apply register_frame_trans (intAssign_register_frame (intAssign_banks _ _ _) "%vp" _ (by decide))
    apply register_frame_trans (intAssign_register_frame (intAssign_banks _ _ _) "%stride" _ (by decide))
    exact intAssign_register_frame (intAssign_banks _ _ _) "%j" _ (by decide)
  refine ⟨s7,hrun,?_⟩
  constructor
  · simpa [s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,loadedFloat,writeFloat,advance] using hi.running
  · simp [s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,assign,loadedFloat,writeFloat,advance,hi.pcValue]
  · simp [s7,s6,s5,s4,s3,s2,s1,intAssign,finishInteger,loadedFloat,writeFloat,threadLayout,ScalarAttentionOuter.queryIndex,hi.queries]
  · simp [s7]
  · simp [s7,s6,s5,s4,s3,s2,s1,threadLayout,hi.n]
  · simp [s7,s6,s5,s4,s3,s2,s1,threadLayout,hi.dim]
  · simp [s7,s6,s5,s4,threadLayout,r]
  · simp [s7,s6,s5,s4,s3,s2,s1,threadLayout,hi.key,hK64]
  · simp [s7,s6,s5,threadLayout,c]
  · simp [s7,s6,threadLayout]
  · simp [s7,s6,s5,s4,s3,s2,s1,threadLayout,hi.outputPointer]
  · exact ((hf "%scale" (by decide)).2).trans (by simp [s1])
  · intro h; exact (h rfl).elim
  · exact run_banks_disjoint hrun hi.banks

end
end Ptx.ScalarAttentionInit
