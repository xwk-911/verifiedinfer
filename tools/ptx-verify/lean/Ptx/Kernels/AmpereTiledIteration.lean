import Ptx.Kernels.AmpereTiledStage
import Ptx.Kernels.AmpereTiledGuard
import Ptx.Kernels.AmpereTiledAdvance

/-! Parameterized execution of one complete 21-instruction K iteration.
Payload/word/MMA answers remain independent. The full kernel proof still needs
entry reconstruction, induction to completion and global memory agreement. -/
namespace Ptx.AmpereTiledIteration
open Ptx.ISA Ptx.Ampere
noncomputable section
abbrev code := Generated.ampere_tiled_matmul.program

def stageState (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) : State :=
  AmpereTiledStage.finalState ctx oracle (AmpereTiledGuard.activeState s) p payload a b
def nextState (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (index : Nat) : State :=
  AmpereTiledAdvance.nextState (stageState ctx oracle s p payload a b) p.a p.ah p.b index

theorem execute (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (pa pb index bound : Nat)
    (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (acc : Fin 4 → ℝ)
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = 57)
    (hindex : lookup "%it" s.scalar.core.thread.regs = some index)
    (hbound : lookup "%k" s.scalar.core.thread.regs = some bound) (hlt : index < bound) (h32 : bound < 2^32)
    (hs : ∀ i, lookup (CopyStage.sourceName i) s.scalar.core.thread.regs = some (CopyStage.source p i))
    (hd : ∀ i, lookup (CopyStage.destinationName i) s.scalar.core.thread.regs = some (CopyStage.destination p i))
    (ha : lookup "%la" s.scalar.core.thread.regs = some pa)
    (hb : lookup "%lb" s.scalar.core.thread.regs = some pb)
    (hc : ∀ i, declarationLookup (MmaBlock.accumulators.get i) s.scalar.floats = some (.f32,acc i))
    (hn : ∀ i, lookup (MmaBlock.accumulators.get i) s.scalar.core.thread.regs = none)
    (hsize : ∀ i, (payload i).length = 8)
    (hq : ∀ i, oracle.bytes (s.scalar.core.queries+i.val) = payload i)
    (hqa : ∀ i, oracle.word32 (s.scalar.core.queries+3+i.val) = .packed (a i))
    (hqb : ∀ i, oracle.word32 (s.scalar.core.queries+7+i.val) = .packed (b i)) :
    Ampere.run ctx oracle code 21 s = .ok (nextState ctx oracle s p payload a b index,
      AmpereTiledStage.events ctx oracle (AmpereTiledGuard.activeState s) p payload pa pb a b acc) := by
  let g := AmpereTiledGuard.activeState s
  let st := AmpereTiledStage.finalState ctx oracle g p payload a b
  have hg := AmpereTiledGuard.active ctx oracle s index bound hr hp hindex hbound hlt h32
  have hgn (name : String) (hne : name ≠ "%p") : lookup name g.scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := by
    simp [g,AmpereTiledGuard.activeState,hne]
  have hstage := AmpereTiledStage.execute ctx oracle g p payload pa pb a b acc
    (by simpa [g,AmpereTiledGuard.activeState] using hr) rfl
    (fun i => by rw [hgn _ (by fin_cases i <;> decide)]; exact hs i)
    (fun i => by rw [hgn _ (by fin_cases i <;> decide)]; exact hd i)
    (by rw [hgn _ (by decide)]; exact ha) (by rw [hgn _ (by decide)]; exact hb)
    (fun i => (AmpereTiledGuard.active_float s _ (by fin_cases i <;> decide) (hn i)).trans (hc i))
    (fun i => by rw [hgn _ (by fin_cases i <;> decide)]; exact hn i)
    hsize (by simpa [g,AmpereTiledGuard.activeState] using hq)
    (by simpa [g,AmpereTiledGuard.activeState] using hqa)
    (by simpa [g,AmpereTiledGuard.activeState] using hqb)
  have hkeep (name : String) (hm : name ∈ ["%a","%ah","%b","%it"]) :
      lookup name st.scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := by
    have hne : name ≠ "%p" := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hm; rcases hm with rfl | rfl | rfl | rfl <;> decide
    have hA : ∀ i, name ≠ MmaBlock.aRegisters.get i := by
      intro i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> fin_cases i <;> decide
    have hB : ∀ i, name ≠ MmaBlock.bRegisters.get i := by
      intro i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> fin_cases i <;> decide
    have hD : name ∉ MmaBlock.accumulators.names := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> decide
    rw [show st = AmpereTiledStage.finalState ctx oracle g p payload a b by rfl,
      AmpereTiledStage.final_register_frame ctx oracle g p payload a b name hA hB hD,hgn _ hne]
  have ht := AmpereTiledAdvance.execute ctx oracle st p.a p.ah p.b index
    (by simpa [st,g,AmpereTiledGuard.activeState] using hr)
    (by simp [st,g,AmpereTiledGuard.activeState])
    (by rw [hkeep "%a" (by simp)]; exact hs 0)
    (by rw [hkeep "%ah" (by simp)]; exact hs 1)
    (by rw [hkeep "%b" (by simp)]; exact hs 2)
    (by rw [hkeep "%it" (by simp)]; exact hindex)
  rw [show 21 = 2+19 by decide,Ampere.run_add,hg]
  simp only [Except.bind,List.nil_append]
  rw [show 19 = 14+5 by decide,Ampere.run_add,hstage]
  simp only [Except.bind]
  rw [ht]
  simp only [Except.bind,List.append_nil]
  rfl

@[simp] theorem final_pc (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (index : Nat) :
    (nextState ctx oracle s p payload a b index).scalar.core.thread.pc = 57 := rfl
@[simp] theorem final_queries (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (index : Nat) :
    (nextState ctx oracle s p payload a b index).scalar.core.queries = s.scalar.core.queries+10 := by
  simp [nextState,stageState,AmpereTiledGuard.activeState]
@[simp] theorem final_groups (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (index : Nat) :
    (nextState ctx oracle s p payload a b index).groups = s.groups+1 := rfl
@[simp] theorem final_mma_calls (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (index : Nat) :
    (nextState ctx oracle s p payload a b index).mmaCalls = s.mmaCalls+1 := rfl


@[simp] theorem final_status (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (index : Nat) :
    (nextState ctx oracle s p payload a b index).scalar.core.thread.status = s.scalar.core.thread.status := by
  simp [nextState,stageState,AmpereTiledGuard.activeState]

theorem final_register_frame (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (index : Nat) (name : String)
    (hp : name ≠ "%p") (ha : name ≠ "%a") (hah : name ≠ "%ah") (hb : name ≠ "%b") (hi : name ≠ "%it")
    (hA : ∀ i, name ≠ MmaBlock.aRegisters.get i) (hB : ∀ i, name ≠ MmaBlock.bRegisters.get i)
    (hD : name ∉ MmaBlock.accumulators.names) :
    lookup name (nextState ctx oracle s p payload a b index).scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := by
  rw [nextState,AmpereTiledAdvance.final_register_frame _ _ _ _ _ name ha hah hb hi,
    stageState,AmpereTiledStage.final_register_frame _ _ _ _ _ _ _ name hA hB hD]
  simp [AmpereTiledGuard.activeState,hp]

theorem final_nat (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (index : Nat) (i : Fin 4) :
    lookup (MmaBlock.accumulators.get i) (nextState ctx oracle s p payload a b index).scalar.core.thread.regs = none := by
  rw [nextState,AmpereTiledAdvance.final_register_frame]
  · exact AmpereTiledStage.final_nat _ _ _ _ _ _ _ i
  all_goals fin_cases i <;> decide

theorem final_accumulator (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (index : Nat) (i : Fin 4) :
    declarationLookup (MmaBlock.accumulators.get i) (nextState ctx oracle s p payload a b index).scalar.floats =
      some (.f32,oracle.matrix (s.scalar.core.queries+9) i) := by
  rw [nextState,AmpereTiledAdvance.final_float_frame]
  · rw [stageState,AmpereTiledStage.final_accumulator]
    simp [AmpereTiledStage.answer,AmpereTiledGuard.activeState,Nat.add_assoc]
  · fin_cases i <;> decide
  · fin_cases i <;> decide
  · fin_cases i <;> decide
  · fin_cases i <;> decide
  · exact AmpereTiledStage.final_nat _ _ _ _ _ _ _ i

theorem final_copy_count (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (index : Nat) :
    (nextState ctx oracle s p payload a b index).copies.length = s.copies.length+3 := by
  change (AmpereTiledStage.finalState ctx oracle (AmpereTiledGuard.activeState s) p payload a b).copies.length = _
  rw [AmpereTiledStage.final_copies]
  simp [AmpereTiledGuard.activeState,Ampere.intPC,Ampere.intAssign]

theorem final_generation (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (index : Nat) :
    Ptx.Event.generation (nextState ctx oracle s p payload a b index).scalar.core 0 = Ptx.Event.generation s.scalar.core 0+2 := by
  change Ptx.Event.generation (AmpereTiledStage.finalState ctx oracle (AmpereTiledGuard.activeState s) p payload a b).scalar.core 0 = _
  rw [AmpereTiledStage.final_generation]
  rfl

end
end Ptx.AmpereTiledIteration
