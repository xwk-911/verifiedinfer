import Ptx.Kernels.AmpereTiledReconstruct

/-! Canonical actual source traces for arbitrary K counts. They retain oracle
answers and give an exact event/state form to every completed source candidate.
This is source reconstruction, not memory/warp admission or matrix correctness. -/
namespace Ptx.AmpereTiledTrace
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec
noncomputable section
abbrev code := Generated.ampere_tiled_matmul.program
abbrev ReplySet (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) :=
  AmpereTiledLoop.Replies (AmpereTiledEntry.loopConfig cfg ctx) oracle

def stateAt (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) : Nat → State
  | 0 => AmpereTiledEntry.ready cfg ctx
  | step+1 => AmpereTiledIteration.nextState ctx oracle (stateAt cfg ctx oracle r step)
      (AmpereTiledLoop.pointersAt (AmpereTiledEntry.loopConfig cfg ctx) step)
      (r.payload step) (r.a step) (r.b step) (16*step)
def cValues (oracle : Oracle) (step : Nat) (i : Fin 4) : ℝ :=
  if step = 0 then 0 else oracle.matrix (10*step-1) i
def stepEvents (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) : List Event :=
  AmpereTiledStage.events ctx oracle (AmpereTiledGuard.activeState (stateAt cfg ctx oracle r step))
    (AmpereTiledLoop.pointersAt (AmpereTiledEntry.loopConfig cfg ctx) step)
    (r.payload step) (AmpereTiledAddresses.la ctx) (AmpereTiledAddresses.lb ctx)
    (r.a step) (r.b step) (cValues oracle step)
def eventsThrough (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) : Nat → List Event
  | 0 => []
  | step+1 => eventsThrough cfg ctx oracle r step ++ stepEvents cfg ctx oracle r step
def exitState (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) : State :=
  AmpereTiledGuard.exitState (stateAt cfg ctx oracle r (cfg.k/16))
def finalState (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) : State :=
  AmpereTiledFinish.finalState (exitState cfg ctx oracle r)
def events (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) : List Event :=
  eventsThrough cfg ctx oracle r (cfg.k/16) ++ AmpereTiledFinish.events (AmpereTiledAddresses.c cfg ctx)
    (AmpereTiledAddresses.ch cfg ctx) (cValues oracle (cfg.k/16))

theorem state_queries (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    (stateAt cfg ctx oracle r step).scalar.core.queries = 10*step := by
  induction step with
  | zero => rfl
  | succ step ih => simp [stateAt,ih,Nat.mul_add,Nat.add_assoc]
theorem state_groups (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    (stateAt cfg ctx oracle r step).groups = step := by induction step with
  | zero => rfl
  | succ step ih => simp [stateAt,ih]
theorem state_mma_calls (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    (stateAt cfg ctx oracle r step).mmaCalls = step := by induction step with
  | zero => rfl
  | succ step ih => simp [stateAt,ih]
theorem state_copy_count (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    (stateAt cfg ctx oracle r step).copies.length = 3*step := by induction step with
  | zero => rfl
  | succ step ih => simp [stateAt,AmpereTiledIteration.final_copy_count,ih,Nat.mul_add]
theorem state_generation (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    Ptx.Event.generation (stateAt cfg ctx oracle r step).scalar.core 0 = 2*step := by induction step with
  | zero => rfl
  | succ step ih => simp [stateAt,AmpereTiledIteration.final_generation,ih,Nat.mul_add]

theorem state_accumulators (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    ∀ i, declarationLookup (MmaBlock.accumulators.get i) (stateAt cfg ctx oracle r step).scalar.floats = some (.f32,cValues oracle step i) := by
  cases step with
  | zero => exact AmpereTiledEntry.zeroed_accumulator _
  | succ step =>
    intro i
    rw [stateAt,AmpereTiledIteration.final_accumulator,state_queries]
    have hq : 10*step+9 = 10*(step+1)-1 := by omega
    simp [cValues,hq]

theorem state_invariant {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle)
    (step : Nat) (hs : step ≤ cfg.k/16) :
    AmpereTiledLoop.Invariant (AmpereTiledEntry.loopConfig cfg ctx) step (stateAt cfg ctx oracle r step) := by
  have hb : 16*(AmpereTiledEntry.loopConfig cfg ctx).tiles < 2^32 := by
    change 16*(cfg.k/16) < 2^32
    have hk := h.tiles.2.2
    have h32 := h.dimensions.2.2
    omega
  induction step with
  | zero => exact AmpereTiledEntry.invariant cfg ctx h.dimensions.2.2 h.tiles.2.2
  | succ step ih => exact AmpereTiledLoop.preserve ctx oracle r (ih (by omega)) (by change step < cfg.k/16; omega) hb

theorem prefix_run {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg)
    (step : Nat) (hs : step ≤ cfg.k/16) :
    Ampere.run ctx oracle code (57+21*step) {} = .ok (stateAt cfg ctx oracle r step,eventsThrough cfg ctx oracle r step) := by
  induction step with
  | zero =>
    have hg := AmpereTiledGeometry.active_guards h hv ha
    exact AmpereTiledEntry.source_prefix cfg ctx oracle hp hg.1 hg.2
  | succ step ih =>
    have hi := state_invariant h ctx oracle r step (by omega)
    have hlt : step < (AmpereTiledEntry.loopConfig cfg ctx).tiles := by change step < cfg.k/16; omega
    have hb : 16*(AmpereTiledEntry.loopConfig cfg ctx).tiles < 2^32 := by
      change 16*(cfg.k/16) < 2^32
      have hk := h.tiles.2.2
      have h32 := h.dimensions.2.2
      omega
    have hstep := AmpereTiledIteration.execute ctx oracle (stateAt cfg ctx oracle r step)
      (AmpereTiledLoop.pointersAt (AmpereTiledEntry.loopConfig cfg ctx) step) (r.payload step)
      (AmpereTiledAddresses.la ctx) (AmpereTiledAddresses.lb ctx) (16*step) (16*(cfg.k/16))
      (r.a step) (r.b step) (cValues oracle step) hi.running hi.pc hi.index (hi.fixed 7)
      (by omega) hb hi.sources (AmpereTiledLoop.destination_lookup hi) (hi.fixed 3) (hi.fixed 4)
      (state_accumulators cfg ctx oracle r step) hi.noInteger (r.size step hlt)
      (by simpa [state_queries,AmpereTiledEntry.loopConfig] using r.bytes step hlt)
      (by simpa [state_queries,AmpereTiledEntry.loopConfig] using r.wordA step hlt)
      (by simpa [state_queries,AmpereTiledEntry.loopConfig] using r.wordB step hlt)
    rw [show 57+21*(step+1) = (57+21*step)+21 by omega,Ampere.run_add,ih (by omega)]
    simp only [Except.bind]
    rw [hstep]
    rfl

theorem translated_run {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) :
    Ampere.run ctx oracle code (64+21*(cfg.k/16)) {} = .ok (finalState cfg ctx oracle r,events cfg ctx oracle r) := by
  let s := stateAt cfg ctx oracle r (cfg.k/16)
  let ex := exitState cfg ctx oracle r
  have hi := state_invariant h ctx oracle r (cfg.k/16) (Nat.le_refl _)
  have hb : 16*(cfg.k/16) < 2^32 := by have hk := h.tiles.2.2; have h32 := h.dimensions.2.2; omega
  have hg := AmpereTiledGuard.exit ctx oracle s (16*(cfg.k/16)) hi.running hi.pc hi.index (hi.fixed 7) hb
  have hn (name : String) (hne : name ≠ "%p") : lookup name ex.scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := by
    simp [ex,exitState,s,AmpereTiledGuard.exitState,hne]
  have hf (i : Fin 4) : declarationLookup (MmaBlock.accumulators.get i) ex.scalar.floats = some (.f32,cValues oracle (cfg.k/16) i) := by
    have hne : MmaBlock.accumulators.get i ≠ "%p" := by fin_cases i <;> decide
    have hni : lookup (MmaBlock.accumulators.get i) s.scalar.core.thread.regs = none := hi.noInteger i
    have hfi := state_accumulators cfg ctx oracle r (cfg.k/16) i
    change declarationLookup (MmaBlock.accumulators.get i) s.scalar.floats = _ at hfi
    change declarationLookup (MmaBlock.accumulators.get i) (AmpereTiledGuard.exitState s).scalar.floats = _
    simpa [AmpereTiledGuard.exitState,Ampere.intPC,Ampere.intAssign,hne,hni] using hfi
  have hout := AmpereTiledFinish.execute ctx oracle ex (AmpereTiledAddresses.c cfg ctx) (AmpereTiledAddresses.ch cfg ctx)
    (cValues oracle (cfg.k/16)) (by simpa [ex,exitState,AmpereTiledGuard.exitState] using hi.running) rfl
    (by rw [hn "%c" (by decide)]; exact hi.fixed 5) (by rw [hn "%ch" (by decide)]; exact hi.fixed 6) hf
  change Ampere.run ctx oracle code 5 (AmpereTiledGuard.exitState s) = _ at hout
  have hfinish : Ampere.run ctx oracle code 7 s = .ok (AmpereTiledFinish.finalState ex,
      AmpereTiledFinish.events (AmpereTiledAddresses.c cfg ctx) (AmpereTiledAddresses.ch cfg ctx) (cValues oracle (cfg.k/16))) := by
    rw [show 7 = 2+5 by decide,Ampere.run_add,hg]
    simp only [Except.bind,List.nil_append]
    rw [hout]
  rw [show 64+21*(cfg.k/16) = (57+21*(cfg.k/16))+7 by omega,Ampere.run_add,
    prefix_run h ctx oracle r hp hv ha _ (Nat.le_refl _)]
  simp only [Except.bind]
  rw [hfinish]
  rfl

theorem complete_source_shape {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg)
    {count last emitted} (hr : Ampere.run ctx oracle code count {} = .ok (last,emitted))
    (hd : last.scalar.core.thread.status = .done) : ∃ r : ReplySet cfg ctx oracle,
    count = 64+21*(cfg.k/16) ∧ last = finalState cfg ctx oracle r ∧ emitted = events cfg ctx oracle r := by
  obtain ⟨r⟩ := AmpereTiledReconstruct.complete_replies h ctx oracle hp hv ha hr hd
  exact ⟨r,Ampere.complete_run_unique hr hd (translated_run h ctx oracle r hp hv ha) rfl⟩

theorem final_metadata (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) :
    (finalState cfg ctx oracle r).copies.length = 3*(cfg.k/16) ∧
      (finalState cfg ctx oracle r).groups = cfg.k/16 ∧ (finalState cfg ctx oracle r).mmaCalls = cfg.k/16 ∧
      Ptx.Event.generation (finalState cfg ctx oracle r).scalar.core 0 = 2*(cfg.k/16) ∧
      (finalState cfg ctx oracle r).scalar.core.queries = 10*(cfg.k/16) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · change (stateAt cfg ctx oracle r (cfg.k/16)).copies.length = _
    exact state_copy_count _ _ _ _ _
  · change (stateAt cfg ctx oracle r (cfg.k/16)).groups = _
    exact state_groups _ _ _ _ _
  · change (stateAt cfg ctx oracle r (cfg.k/16)).mmaCalls = _
    exact state_mma_calls _ _ _ _ _
  · change Ptx.Event.generation (stateAt cfg ctx oracle r (cfg.k/16)).scalar.core 0 = _
    exact state_generation _ _ _ _ _
  · change (stateAt cfg ctx oracle r (cfg.k/16)).scalar.core.queries = _
    exact state_queries _ _ _ _ _

theorem complete_metadata {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg)
    {count last emitted} (hr : Ampere.run ctx oracle code count {} = .ok (last,emitted))
    (hd : last.scalar.core.thread.status = .done) :
    last.copies.length = 3*(cfg.k/16) ∧ last.groups = cfg.k/16 ∧ last.mmaCalls = cfg.k/16 ∧
      Ptx.Event.generation last.scalar.core 0 = 2*(cfg.k/16) ∧ last.scalar.core.queries = 10*(cfg.k/16) := by
  obtain ⟨r,_,hs,_⟩ := complete_source_shape h ctx oracle hp hv ha hr hd
  rw [hs]
  exact final_metadata _ _ _ _

theorem candidate_trace_shape {cfg : Config} (h : Layout cfg) {launch : Scalar.Launch} {candidate : Candidate} {t : ThreadTrace}
    (hp : AmpereTiledInit.Params cfg launch.params) (hg : launch.geometry = geometry cfg) (ha : Active cfg)
    (hw : WellFormed code launch candidate) (hc : Complete candidate) (ht : t ∈ candidate.traces) :
    let ctx : Scalar.Context := {id := t.id,params := launch.params,block := launch.geometry.block}
    ∃ r : ReplySet cfg ctx t.oracle, t.count = 64+21*(cfg.k/16) ∧
      t.final = finalState cfg ctx t.oracle r ∧ t.events = events cfg ctx t.oracle r := by
  have hi := hw.2.2.1 t ht
  exact complete_source_shape h _ t.oracle hp (by simpa only [hg] using hi.1) ha hi.2 (hc t ht)

end
end Ptx.AmpereTiledTrace
