import Ptx.Kernels.AmpereTiledIteration
import Ptx.Kernels.AmpereTiledFinish

/-! Arbitrarily many actual K iterations, from PC 57 through the source stores
and return. Reply obligations constrain sizes/tags only, never read/MMA values.
The invariant is an entry reconstruction obligation, not a kernel precondition.
Memory/warp admission and the PC-zero prefix remain separate proof duties. -/
namespace Ptx.AmpereTiledLoop
open Ptx.ISA Ptx.Ampere
noncomputable section
abbrev code := Generated.ampere_tiled_matmul.program

structure Config where
  pointers : CopyStage.Pointers
  pa : Nat
  pb : Nat
  low : Nat
  high : Nat
  tiles : Nat
  firstQuery : Nat

def pointersAt (cfg : Config) (step : Nat) : CopyStage.Pointers := {
  cfg.pointers with
  a := wrap 64 (cfg.pointers.a+32*step)
  ah := wrap 64 (cfg.pointers.ah+32*step)
  b := wrap 64 (cfg.pointers.b+32*step)
}
def fixedName (i : Fin 8) : String :=
  if i.val = 0 then "%sa" else if i.val = 1 then "%sah" else if i.val = 2 then "%sb"
  else if i.val = 3 then "%la" else if i.val = 4 then "%lb" else if i.val = 5 then "%c"
  else if i.val = 6 then "%ch" else "%k"
def fixedValue (cfg : Config) (i : Fin 8) : Nat :=
  if i.val = 0 then cfg.pointers.sa else if i.val = 1 then cfg.pointers.sah else if i.val = 2 then cfg.pointers.sb
  else if i.val = 3 then cfg.pa else if i.val = 4 then cfg.pb else if i.val = 5 then cfg.low
  else if i.val = 6 then cfg.high else 16*cfg.tiles

structure Invariant (cfg : Config) (step : Nat) (s : State) : Prop where
  running : s.scalar.core.thread.status = .running
  pc : s.scalar.core.thread.pc = 57
  index : lookup "%it" s.scalar.core.thread.regs = some (16*step)
  sources : ∀ i, lookup (CopyStage.sourceName i) s.scalar.core.thread.regs = some (CopyStage.source (pointersAt cfg step) i)
  fixed : ∀ i, lookup (fixedName i) s.scalar.core.thread.regs = some (fixedValue cfg i)
  query : s.scalar.core.queries = cfg.firstQuery+10*step
  accumulators : ∃ acc : Fin 4 → ℝ, ∀ i, declarationLookup (MmaBlock.accumulators.get i) s.scalar.floats = some (.f32,acc i)
  noInteger : ∀ i, lookup (MmaBlock.accumulators.get i) s.scalar.core.thread.regs = none

structure Replies (cfg : Config) (oracle : Oracle) where
  payload : Nat → Fin 3 → List Symbolic.Byte
  a : Nat → Fin 4 → PackedF16
  b : Nat → Fin 2 → PackedF16
  size : ∀ step, step < cfg.tiles → ∀ i, (payload step i).length = 8
  bytes : ∀ step, step < cfg.tiles → ∀ i, oracle.bytes (cfg.firstQuery+10*step+i.val) = payload step i
  wordA : ∀ step, step < cfg.tiles → ∀ i, oracle.word32 (cfg.firstQuery+10*step+3+i.val) = .packed (a step i)
  wordB : ∀ step, step < cfg.tiles → ∀ i, oracle.word32 (cfg.firstQuery+10*step+7+i.val) = .packed (b step i)

theorem destination_lookup {cfg step s} (h : Invariant cfg step s) (i : Fin 3) :
    lookup (CopyStage.destinationName i) s.scalar.core.thread.regs = some (CopyStage.destination (pointersAt cfg step) i) := by
  fin_cases i
  · exact h.fixed 0
  · exact h.fixed 1
  · exact h.fixed 2

theorem pointer_step (base step : Nat) :
    wrap 64 (wrap 64 (base+32*step)+32) = wrap 64 (base+32*(step+1)) := by
  rw [Scalar.wrap_add_left]
  congr 1

theorem fixed_frame (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : CopyStage.Pointers)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (index : Nat) (i : Fin 8) :
    lookup (fixedName i) (AmpereTiledIteration.nextState ctx oracle s p payload a b index).scalar.core.thread.regs =
      lookup (fixedName i) s.scalar.core.thread.regs := by
  apply AmpereTiledIteration.final_register_frame
  all_goals first | (fin_cases i <;> decide) | (intro j; fin_cases i <;> fin_cases j <;> decide)

theorem preserve_values {cfg : Config} (ctx : Scalar.Context) (oracle : Oracle)
    (payload : Fin 3 → List Symbolic.Byte) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16)
    {step s} (h : Invariant cfg step s) (hlt : step < cfg.tiles) (h32 : 16*cfg.tiles < 2^32) :
    Invariant cfg (step+1) (AmpereTiledIteration.nextState ctx oracle s (pointersAt cfg step)
      payload a b (16*step)) := by
  let p := pointersAt cfg step
  let st := AmpereTiledIteration.stageState ctx oracle s p payload a b
  have hptr := AmpereTiledAdvance.final_pointers st p.a p.ah p.b (16*step)
  have hindex : wrap 32 (16*step+16) = 16*(step+1) := by
    have he : wrap 32 (16*step+16) = 16*step+16 := Nat.mod_eq_of_lt (by omega)
    simpa [Nat.mul_add,Nat.mul_one] using he
  refine ⟨by simpa using h.running,by simp,?_,?_,?_,?_,?_,?_⟩
  · simpa [AmpereTiledIteration.nextState,hindex,Nat.mul_add,Nat.mul_one] using hptr.2.2.2
  · intro i
    fin_cases i
    · simpa [st,p,pointersAt,CopyStage.sourceName,CopyStage.source,pointer_step,AmpereTiledIteration.nextState] using hptr.1
    · simpa [st,p,pointersAt,CopyStage.sourceName,CopyStage.source,pointer_step,AmpereTiledIteration.nextState] using hptr.2.1
    · simpa [st,p,pointersAt,CopyStage.sourceName,CopyStage.source,pointer_step,AmpereTiledIteration.nextState] using hptr.2.2.1
  · intro i
    rw [fixed_frame]
    exact h.fixed i
  · simp [h.query,Nat.mul_add,Nat.mul_one,Nat.add_assoc]
  · exact ⟨oracle.matrix (s.scalar.core.queries+9),AmpereTiledIteration.final_accumulator _ _ _ _ _ _ _ _⟩
  · exact AmpereTiledIteration.final_nat _ _ _ _ _ _ _ _

theorem preserve {cfg : Config} (ctx : Scalar.Context) (oracle : Oracle) (replies : Replies cfg oracle)
    {step s} (h : Invariant cfg step s) (hlt : step < cfg.tiles) (h32 : 16*cfg.tiles < 2^32) :
    Invariant cfg (step+1) (AmpereTiledIteration.nextState ctx oracle s (pointersAt cfg step)
      (replies.payload step) (replies.a step) (replies.b step) (16*step)) :=
  preserve_values ctx oracle (replies.payload step) (replies.a step) (replies.b step) h hlt h32

theorem iteration {cfg : Config} (ctx : Scalar.Context) (oracle : Oracle) (replies : Replies cfg oracle)
    {step s} (h : Invariant cfg step s) (hlt : step < cfg.tiles) (h32 : 16*cfg.tiles < 2^32) :
    ∃ next emitted, Ampere.run ctx oracle code 21 s = .ok (next,emitted) ∧
      Invariant cfg (step+1) next ∧ emitted.length = 17 := by
  obtain ⟨acc,hacc⟩ := h.accumulators
  refine ⟨_,_,AmpereTiledIteration.execute ctx oracle s (pointersAt cfg step) (replies.payload step)
    cfg.pa cfg.pb (16*step) (16*cfg.tiles) (replies.a step) (replies.b step) acc
    h.running h.pc h.index (h.fixed 7) (by omega) h32 h.sources (destination_lookup h)
    (h.fixed 3) (h.fixed 4) hacc h.noInteger (replies.size step hlt)
    (by simpa [h.query] using replies.bytes step hlt)
    (by simpa [h.query] using replies.wordA step hlt)
    (by simpa [h.query] using replies.wordB step hlt),preserve ctx oracle replies h hlt h32,?_⟩
  exact AmpereTiledStage.events_length _ _ _ _ _ _ _ _ _ _

theorem finish {cfg : Config} (ctx : Scalar.Context) (oracle : Oracle) {s : State}
    (h : Invariant cfg cfg.tiles s) (h32 : 16*cfg.tiles < 2^32) :
    ∃ last emitted, Ampere.run ctx oracle code 7 s = .ok (last,emitted) ∧
      last.scalar.core.thread.status = .done ∧ emitted.length = 4 ∧
      last.scalar.core.queries = cfg.firstQuery+10*cfg.tiles := by
  obtain ⟨acc,hacc⟩ := h.accumulators
  let ex := AmpereTiledGuard.exitState s
  have hn (name : String) (hne : name ≠ "%p") : lookup name ex.scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := by
    simp [ex,AmpereTiledGuard.exitState,hne]
  have hf (i : Fin 4) : declarationLookup (MmaBlock.accumulators.get i) ex.scalar.floats = some (.f32,acc i) := by
    have hne : MmaBlock.accumulators.get i ≠ "%p" := by fin_cases i <;> decide
    simpa [ex,AmpereTiledGuard.exitState,Ampere.intPC,Ampere.intAssign,hne,h.noInteger i] using hacc i
  have hguard := AmpereTiledGuard.exit ctx oracle s (16*cfg.tiles) h.running h.pc h.index (h.fixed 7) h32
  have hfinish := AmpereTiledFinish.execute ctx oracle ex cfg.low cfg.high acc
    (by simpa [ex,AmpereTiledGuard.exitState] using h.running) rfl
    (by rw [hn "%c" (by decide)]; exact h.fixed 5)
    (by rw [hn "%ch" (by decide)]; exact h.fixed 6) hf
  refine ⟨AmpereTiledFinish.finalState ex,AmpereTiledFinish.events cfg.low cfg.high acc,?_,rfl,rfl,?_⟩
  · rw [show 7 = 2+5 by decide,Ampere.run_add,hguard]
    simp only [Except.bind,List.nil_append]
    rw [hfinish]
  · simpa [ex,AmpereTiledGuard.exitState] using h.query

/-- Local source completion for an arbitrary remaining iteration count. This
constructs a trace from shape-correct replies, with no memory/arithmetic claim. -/
theorem run_to_completion {cfg : Config} (ctx : Scalar.Context) (oracle : Oracle) (replies : Replies cfg oracle)
    (h32 : 16*cfg.tiles < 2^32) (remaining : Nat) {step s}
    (hcount : step+remaining = cfg.tiles) (h : Invariant cfg step s) :
    ∃ last emitted, Ampere.run ctx oracle code (21*remaining+7) s = .ok (last,emitted) ∧
      last.scalar.core.thread.status = .done ∧ emitted.length = 17*remaining+4 ∧
      last.scalar.core.queries = cfg.firstQuery+10*cfg.tiles := by
  induction remaining generalizing step s with
  | zero =>
    have he : step = cfg.tiles := by omega
    subst step
    simpa using finish ctx oracle h h32
  | succ remaining ih =>
    obtain ⟨mid,headEvents,hhead,hm,hlen⟩ := iteration ctx oracle replies h (by omega) h32
    obtain ⟨last,tailEvents,htail,hd,htlen,hq⟩ := ih (step := step+1) (by omega) hm
    refine ⟨last,headEvents++tailEvents,?_,hd,?_,hq⟩
    · rw [show 21*(remaining+1)+7 = 21+(21*remaining+7) by omega,Ampere.run_add,hhead]
      simp only [Except.bind]
      rw [htail]
    · simp only [List.length_append,hlen,htlen]
      omega

/-- Any other completed local source run has exactly the reconstructed count,
event count and query count. This remains conditional on reply tags/sizes. -/
theorem complete_run_counts {cfg : Config} (ctx : Scalar.Context) (oracle : Oracle) (replies : Replies cfg oracle)
    (h32 : 16*cfg.tiles < 2^32) (remaining : Nat) {step s count last emitted}
    (hcount : step+remaining = cfg.tiles) (h : Invariant cfg step s)
    (hrun : Ampere.run ctx oracle code count s = .ok (last,emitted))
    (hdone : last.scalar.core.thread.status = .done) :
    count = 21*remaining+7 ∧ emitted.length = 17*remaining+4 ∧
      last.scalar.core.queries = cfg.firstQuery+10*cfg.tiles := by
  obtain ⟨final,events,hr,hf,he,hq⟩ := run_to_completion ctx oracle replies h32 remaining hcount h
  obtain ⟨hc,hs,hl⟩ := Ampere.complete_run_unique hrun hdone hr hf
  exact ⟨hc,hl ▸ he,hs ▸ hq⟩

end
end Ptx.AmpereTiledLoop
