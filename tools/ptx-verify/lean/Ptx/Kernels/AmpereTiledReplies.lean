import Ptx.Kernels.AmpereTiledLoop
import Ptx.Ampere.CopyInversion
import Ptx.Ampere.RawLoads

/-! Reply sizes/tags forced by arbitrary actual completed K-loop executions.
No read values, matrix answers, memory graph or chosen legal witness is assumed. -/
namespace Ptx.AmpereTiledReplies
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledLoop
noncomputable section

structure Shape (oracle : Oracle) (query : Nat) : Prop where
  bytes : ∀ i : Fin 3, (oracle.bytes (query+i.val)).length = 8
  a : ∀ i : Fin 4, ∃ pair, oracle.word32 (query+3+i.val) = .packed pair
  b : ∀ i : Fin 2, ∃ pair, oracle.word32 (query+7+i.val) = .packed pair

theorem step_shape {cfg : Config} (ctx : Scalar.Context) (oracle : Oracle) {step s count last emitted}
    (h : Invariant cfg step s) (hlt : step < cfg.tiles) (h32 : 16*cfg.tiles < 2^32)
    (hc : Ampere.run ctx oracle code count s = .ok (last,emitted)) (hd : last.scalar.core.thread.status = .done) :
    Shape oracle s.scalar.core.queries := by
  let p := pointersAt cfg step
  let g := AmpereTiledGuard.activeState s
  have hg := AmpereTiledGuard.active ctx oracle s (16*step) (16*cfg.tiles)
    h.running h.pc h.index (h.fixed 7) (by omega) h32
  have hgr : g.scalar.core.thread.status = .running := by simpa [g,AmpereTiledGuard.activeState] using h.running
  have hgn (name : String) (hne : name ≠ "%p") : lookup name g.scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := by
    simp [g,AmpereTiledGuard.activeState,hne]
  have hsrc : ∀ i, lookup (CopyStage.sourceName i) g.scalar.core.thread.regs = some (CopyStage.source p i) := by
    intro i
    rw [hgn _ (by fin_cases i <;> decide)]
    exact h.sources i
  have hdst : ∀ i, lookup (CopyStage.destinationName i) g.scalar.core.thread.regs = some (CopyStage.destination p i) := by
    intro i
    rw [hgn _ (by fin_cases i <;> decide)]
    exact destination_lookup h i
  obtain ⟨nc,ec,_,htc,_⟩ := completed_tail hc hg (Nat.le_of_lt (completed_after_running_prefix hc hd hg hgr))
  have hsize := CopyStage.completed_sizes AmpereTiledStage.copy_fragment hgr rfl hsrc hdst htc hd
  let payload (i : Fin 3) := oracle.bytes (g.scalar.core.queries+i.val)
  have hcopy := CopyStage.execute AmpereTiledStage.copy_fragment ctx oracle g p payload hgr rfl hsrc hdst hsize (fun _ => rfl)
  have hpr : (CopyStage.prepared ctx g p payload).scalar.core.thread.status = .running := by simpa using hgr
  obtain ⟨nm,em,_,htm,_⟩ := completed_tail htc hcopy (Nat.le_of_lt (completed_after_running_prefix htc hd hcopy hpr))
  have hwords := RawLoads.packed_of_mma AmpereTiledStage.mma_fragment hpr (by simp [g,AmpereTiledGuard.activeState])
    (by simp only [CopyStage.prepared_nat]; rw [hgn "%la" (by decide)]; exact h.fixed 3)
    (by simp only [CopyStage.prepared_nat]; rw [hgn "%lb" (by decide)]; exact h.fixed 4) htm hd
  refine ⟨?_,?_,?_⟩
  · simpa [g,AmpereTiledGuard.activeState] using hsize
  · simpa [g,AmpereTiledGuard.activeState,Nat.add_assoc] using hwords.1
  · simpa [g,AmpereTiledGuard.activeState,Nat.add_assoc] using hwords.2

def aValues {oracle query} (h : Shape oracle query) (i : Fin 4) : PackedF16 := Classical.choose (h.a i)
def bValues {oracle query} (h : Shape oracle query) (i : Fin 2) : PackedF16 := Classical.choose (h.b i)
theorem a_values {oracle query} (h : Shape oracle query) (i : Fin 4) :
    oracle.word32 (query+3+i.val) = .packed (aValues h i) := Classical.choose_spec (h.a i)
theorem b_values {oracle query} (h : Shape oracle query) (i : Fin 2) :
    oracle.word32 (query+7+i.val) = .packed (bValues h i) := Classical.choose_spec (h.b i)

theorem iteration_from_complete {cfg : Config} (ctx : Scalar.Context) (oracle : Oracle) {step s count last emitted}
    (h : Invariant cfg step s) (hlt : step < cfg.tiles) (h32 : 16*cfg.tiles < 2^32)
    (hc : Ampere.run ctx oracle code count s = .ok (last,emitted)) (hd : last.scalar.core.thread.status = .done) :
    ∃ next head, Ampere.run ctx oracle code 21 s = .ok (next,head) ∧ Invariant cfg (step+1) next ∧
      Shape oracle s.scalar.core.queries := by
  have hs := step_shape ctx oracle h hlt h32 hc hd
  let payload (i : Fin 3) := oracle.bytes (s.scalar.core.queries+i.val)
  obtain ⟨acc,hacc⟩ := h.accumulators
  refine ⟨_,_,AmpereTiledIteration.execute ctx oracle s (pointersAt cfg step) payload cfg.pa cfg.pb
    (16*step) (16*cfg.tiles) (aValues hs) (bValues hs) acc h.running h.pc h.index (h.fixed 7)
    (by omega) h32 h.sources (destination_lookup h) (h.fixed 3) (h.fixed 4) hacc h.noInteger
    hs.bytes (fun _ => rfl) (a_values hs) (b_values hs),?_,hs⟩
  exact preserve_values ctx oracle payload (aValues hs) (bValues hs) h hlt h32

theorem suffix_shapes {cfg : Config} (ctx : Scalar.Context) (oracle : Oracle) (remaining : Nat)
    {step s count last emitted} (hcount : step+remaining = cfg.tiles)
    (h : Invariant cfg step s) (h32 : 16*cfg.tiles < 2^32)
    (hc : Ampere.run ctx oracle code count s = .ok (last,emitted)) (hd : last.scalar.core.thread.status = .done) :
    ∀ index, step ≤ index → index < cfg.tiles → Shape oracle (cfg.firstQuery+10*index) := by
  induction remaining generalizing step s count emitted with
  | zero => intro index hlo hhi; omega
  | succ remaining ih =>
    obtain ⟨mid,head,hhead,hm,hs⟩ := iteration_from_complete ctx oracle h (by omega) h32 hc hd
    obtain ⟨nr,er,_,ht,_⟩ := completed_tail hc hhead (Nat.le_of_lt (completed_after_running_prefix hc hd hhead hm.running))
    have hrest := ih (step := step+1) (by omega) hm ht
    intro index hlo hhi
    by_cases he : index = step
    · subst index
      simpa only [h.query] using hs
    · exact hrest index (by omega) hhi

def fromShapes (cfg : Config) (oracle : Oracle) (h : ∀ step, step < cfg.tiles → Shape oracle (cfg.firstQuery+10*step)) :
    Replies cfg oracle := {
  payload := fun step i => oracle.bytes (cfg.firstQuery+10*step+i.val)
  a := fun step i => if ht : step < cfg.tiles then aValues (h step ht) i else ⟨0,0⟩
  b := fun step i => if ht : step < cfg.tiles then bValues (h step ht) i else ⟨0,0⟩
  size := fun step ht => (h step ht).bytes
  bytes := fun _ _ _ => rfl
  wordA := by intro step ht i; simp only [dite_eq_left ht]; exact a_values (h step ht) i
  wordB := by intro step ht i; simp only [dite_eq_left ht]; exact b_values (h step ht) i
}

end
end Ptx.AmpereTiledReplies
