import Ptx.Kernels.ScalarAttentionUpdate
import Ptx.Scalar.Control

/-! Actual value-load and first-item/update branch at PCs 53--68. The first
item may enter with uninitialized softmax registers. This is local execution;
the value reply is not assumed to be justified by global memory consistency. -/
namespace Ptx.ScalarAttentionOuterUpdate
open Ptx.ISA Ptx.Scalar
noncomputable section
abbrev code := Generated.scalar_flash_attention.program
def changed : List String := ["%vv","%p","%nextm","%a","%w","%max","%l","%u"]

structure Finished (score value : Nat → ℝ) (j query : Nat) (s : Scalar.State) : Prop where
  running : s.core.thread.status = .running
  pc : s.core.thread.pc = 69
  queries : s.core.queries = query+1
  online : ScalarAttentionUpdate.Registers s (OnlineSoftmax.run score value (j+1))
  banks : BanksDisjoint s

theorem value_and_update (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (score value : Nat → ℝ) (j address : Nat) (s : Scalar.State)
    (hr : s.core.thread.status = .running) (hp : s.core.thread.pc = 53)
    (hj32 : j < 2^32) (ha64 : address < 2^64)
    (hj : lookup "%j" s.core.thread.regs = some j)
    (ha : lookup "%vp" s.core.thread.regs = some (wrap 64 address))
    (hs : declarationLookup "%score" s.floats = some (.f32,score j))
    (honline : j ≠ 0 → ScalarAttentionUpdate.Registers s (OnlineSoftmax.run score value j))
    (hbank : BanksDisjoint s) (ho : oracle s.core.queries = .real .f32 (value j)) :
    ∃ final, Scalar.run ctx oracle code (if j = 0 then 6 else 13) s =
      .ok (final,[.read ⟨.global,address⟩ (Symbolic.encode .f32 (value j))]) ∧
      Finished score value j s.core.queries final ∧ RegisterFrame changed s final := by
  let s1 := loadedFloat s "%vv" (value j)
  let s2 := intAssign s1 "%p" (if j = 0 then 1 else 0)
  let s3 := intPC s2 (if j = 0 then 66 else 56)
  have h53 : Scalar.step ctx oracle code s = .ok
      (s1,[.read ⟨.global,address⟩ (Symbolic.encode .f32 (value j))]) := by
    apply load_step (format := .f32) (space := .global) (dst := "%vv")
      (address := {base := .reg "%vp"}) (addr := address) (value := value j) hr (by rw [hp]; rfl)
    · simp [evalAddr,Ptx.eval,ha,show wrap 64 address = address from Nat.mod_eq_of_lt ha64,
        bind,Except.bind,pure,Except.pure]
    · exact ho
  have h54 : Scalar.run ctx oracle code 2 s1 = .ok (s3,[]) := by
    have he := eq_branch_run (ctx := ctx) (oracle := oracle) (code := code) (s := s1)
      (lhs := .reg "%j") (rhs := .imm 0) (pred := "%p") (target := 66) (x := j) (y := 0)
      (by simpa [s1,loadedFloat,writeFloat,advance] using hr)
      (by simp only [s1,loadedFloat,writeFloat,advance,hp]; rfl)
      (by simp only [s1,loadedFloat,writeFloat,advance,hp]; rfl)
      (by simp [Ptx.eval,s1,hj]) rfl hj32 (by decide)
    simpa only [s3,s2,s1,loadedFloat,writeFloat,advance,hp] using he
  have hload : Scalar.run ctx oracle code 1 s = .ok
      (s1,[.read ⟨.global,address⟩ (Symbolic.encode .f32 (value j))]) := by
    simp [Scalar.run,h53,Except.bind]
  have hprefix : Scalar.run ctx oracle code 3 s = .ok
      (s3,[.read ⟨.global,address⟩ (Symbolic.encode .f32 (value j))]) := by
    rw [show 3 = 1+2 by decide,Scalar.run_add,hload]
    simp only [Except.bind,h54,List.append_nil]
  have hf : RegisterFrame ["%vv","%p"] s s3 := by
    apply register_frame_trans (loadedFloat_register_frame s "%vv" _ (by decide))
    apply register_frame_trans (intAssign_register_frame (loadedFloat_banks hbank _ _) "%p" _ (by decide))
    exact intPC_register_frame (intAssign_banks _ _ _) _
  have hfwide : RegisterFrame changed s s3 := register_frame_mono hf (by simp [List.Subset,changed])
  have hr3 : s3.core.thread.status = .running := by
    simpa [s3,s2,s1,intPC,intAssign,finishInteger,loadedFloat,writeFloat,assign,advance] using hr
  have hs3 : declarationLookup "%score" s3.floats = some (.f32,score j) :=
    ((hf "%score" (by decide)).2).trans hs
  have hv3 : declarationLookup "%vv" s3.floats = some (.f32,value j) := by
    simp [s3,s2,s1]
  by_cases hz : j = 0
  · subst j
    let final := ScalarAttentionUpdate.afterInitial s3 (score 0) (value 0)
    have hinit : Scalar.run ctx oracle code 3 s3 = .ok (final,[]) :=
      ScalarAttentionUpdate.initial_block ctx oracle s3 (score 0) (value 0)
        hr3 (by simp [s3,intPC,finishInteger]) hs3 hv3
    have hrun : Scalar.run ctx oracle code 6 s = .ok
        (final,[.read ⟨.global,address⟩ (Symbolic.encode .f32 (value 0))]) := by
      rw [show 6 = 3+3 by decide,Scalar.run_add,hprefix]
      simp [hinit,Except.bind,final]
    have hfinalFrame : RegisterFrame changed s3 final := register_frame_mono
      (ScalarAttentionUpdate.initial_frame s3 (score 0) (value 0)) (by simp [List.Subset,changed])
    refine ⟨final,by simpa using hrun,?_,register_frame_trans hfwide hfinalFrame⟩
    constructor
    · simpa [final,ScalarAttentionUpdate.afterInitial,writeFloat,advance] using hr3
    · simp [final,ScalarAttentionUpdate.afterInitial,writeFloat,advance,s3,intPC,finishInteger]
    · rfl
    · exact ScalarAttentionUpdate.initial_registers _ _ _
    · exact run_banks_disjoint hrun hbank
  · let old := OnlineSoftmax.run score value j
    let mid := ScalarAttentionUpdate.afterUpdate s3 old (score j) (value j)
    let final := intPC mid 69
    have hregs : ScalarAttentionUpdate.Registers s3 old := by
      obtain ⟨hm,hl,hu⟩ := honline hz
      exact ⟨((hf "%max" (by decide)).2).trans hm,
        ((hf "%l" (by decide)).2).trans hl,((hf "%u" (by decide)).2).trans hu⟩
    have hupdate : Scalar.run ctx oracle code 9 s3 = .ok (mid,[]) :=
      ScalarAttentionUpdate.update_block ctx oracle s3 old (score j) (value j)
        hr3 (by simp [s3,intPC,finishInteger,hz]) hregs hs3 hv3
    have hmidBank : BanksDisjoint mid := run_banks_disjoint hupdate (intPC_banks _ _)
    have hmidPc : mid.core.thread.pc = 65 := ScalarAttentionUpdate.update_pc _ _ _ _
      (by simp [s3,intPC,finishInteger,hz])
    have h65 : Scalar.step ctx oracle code mid = .ok (final,[]) := by
      apply integer_local_step (instruction := .jump 69)
        (by simpa [mid,ScalarAttentionUpdate.afterUpdate,writeFloat,advance] using hr3)
        (by rw [hmidPc]; rfl)
        rfl (by intro bid h; cases h)
      rfl
    have hrun : Scalar.run ctx oracle code 13 s = .ok
        (final,[.read ⟨.global,address⟩ (Symbolic.encode .f32 (value j))]) := by
      rw [show 13 = 3+(9+1) by decide,Scalar.run_add,hprefix]
      simp only [Except.bind]
      rw [Scalar.run_add,hupdate]
      simp [Scalar.run,h65,Except.bind]
    have hmidFrame : RegisterFrame changed s3 mid := register_frame_mono
      (ScalarAttentionUpdate.update_frame _ _ _ _) (by simp [List.Subset,ScalarAttentionUpdate.changed,changed])
    have hlastFrame : RegisterFrame [] mid final := intPC_register_frame hmidBank 69
    have hlastOnline := ScalarAttentionUpdate.update_registers s3 old (score j) (value j)
    have honlineFinal : ScalarAttentionUpdate.Registers final (OnlineSoftmax.run score value (j+1)) := by
      rw [OnlineSoftmax.run,ite_eq_right hz]
      exact ⟨((hlastFrame "%max" (by decide)).2).trans hlastOnline.1,
        ((hlastFrame "%l" (by decide)).2).trans hlastOnline.2.1,
        ((hlastFrame "%u" (by decide)).2).trans hlastOnline.2.2⟩
    refine ⟨final,by simpa [hz] using hrun,?_,register_frame_trans hfwide
      (register_frame_trans hmidFrame (intPC_register_frame hmidBank 69))⟩
    constructor
    · simpa [final,intPC,finishInteger,mid,ScalarAttentionUpdate.afterUpdate,writeFloat,advance] using hr3
    · rfl
    · rfl
    · exact honlineFinal
    · exact intPC_banks _ _

end
end Ptx.ScalarAttentionOuterUpdate
