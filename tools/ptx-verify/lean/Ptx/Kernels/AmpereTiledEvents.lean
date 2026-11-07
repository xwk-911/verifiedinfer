import Ptx.Kernels.AmpereTiledTrace
import Ptx.Kernels.AmpereTiledBounds

/-! Actual per-phase event tags, identities and arithmetic inputs. Matrix
results remain oracle answers; checked memory/warp rules must force correctness. -/
namespace Ptx.AmpereTiledEvents
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace
noncomputable section

def current (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :=
  AmpereTiledGuard.activeState (stateAt cfg ctx oracle r step)
def operationAt (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) (part : Fin 3) : Copy :=
  CopyStage.operation ctx (current cfg ctx oracle r step) (AmpereTiledLoop.pointersAt (AmpereTiledEntry.loopConfig cfg ctx) step) (r.payload step) part
def callAt (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) : MmaCall :=
  AmpereTiledStage.call ctx oracle (current cfg ctx oracle r step)
    (AmpereTiledLoop.pointersAt (AmpereTiledEntry.loopConfig cfg ctx) step) (r.payload step) (r.a step) (r.b step) (cValues oracle step)

theorem operation_group (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) (part : Fin 3) :
    (operationAt cfg ctx oracle r step part).group = step := by
  change (stateAt cfg ctx oracle r step).groups = step
  exact state_groups _ _ _ _ _
theorem operation_bytes (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle)
    (step : Nat) (hs : step < cfg.k/16) (part : Fin 3) :
    (operationAt cfg ctx oracle r step part).bytes = oracle.bytes (10*step+part.val) := by
  have ht : step < (AmpereTiledEntry.loopConfig cfg ctx).tiles := hs
  change r.payload step part = _
  simpa [AmpereTiledEntry.loopConfig] using (r.bytes step ht part).symm
theorem operation_size (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle)
    (step : Nat) (hs : step < cfg.k/16) (part : Fin 3) :
    (operationAt cfg ctx oracle r step part).bytes.length = 8 := r.size step hs part
theorem operation_source {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle)
    (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) (step : Nat) (hs : step < cfg.k/16) (part : Fin 3) :
    (operationAt cfg ctx oracle r step part).src = ⟨.global,AmpereTiledBounds.copyStart cfg ctx step part⟩ :=
  AmpereTiledBounds.copy_source h hv ha hs _ _ part
theorem operation_destination {cfg : Config} (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle)
    (hv : ctx.id.Valid (geometry cfg)) (step : Nat) (part : Fin 3) :
    (operationAt cfg ctx oracle r step part).dst =
      ⟨.shared ctx.id.cta,Tiled.copyBase ⟨ctx.id.tid.x,hv.2.1⟩ ⟨ctx.id.tid.y,hv.2.2.1⟩ part⟩ :=
  AmpereTiledAddressRules.copy_destination hv.2.1 hv.2.2.1 _ _ step part

theorem call_pc (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    (callAt cfg ctx oracle r step).pc = 71 := by
  simp [callAt,AmpereTiledStage.call,AmpereTiledStage.loaded,makeMmaCall,current,AmpereTiledGuard.activeState]
theorem call_ordinal (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    (callAt cfg ctx oracle r step).ordinal = step := by
  change (stateAt cfg ctx oracle r step).mmaCalls = step
  exact state_mma_calls cfg ctx oracle r step
theorem call_output (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    (callAt cfg ctx oracle r step).output = oracle.matrix (10*step+9) := by
  simp [callAt,AmpereTiledStage.call,AmpereTiledStage.answer,makeMmaCall,current,AmpereTiledGuard.activeState,state_queries,Nat.add_assoc]
theorem call_old_c (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    (callAt cfg ctx oracle r step).inputs.c = cValues oracle step :=
  MmaBlock.inputs_c _ _ _

theorem phase_events (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    stepEvents cfg ctx oracle r step = [
      .issue (3*step) (operationAt cfg ctx oracle r step 0),
      .issue (3*step+1) (operationAt cfg ctx oracle r step 1),
      .issue (3*step+2) (operationAt cfg ctx oracle r step 2),
      .commit step,.wait (step+1) 0,
      .ordinary (.barrierArrival 0 (2*step)),.ordinary (.barrierReturn 0 (2*step))] ++
      MmaBlock.readEvents ctx (AmpereTiledAddresses.la ctx) (AmpereTiledAddresses.lb ctx) (r.a step) (r.b step) ++ [
      .mmaEntry (callAt cfg ctx oracle r step),.mmaReturn (callAt cfg ctx oracle r step),
      .ordinary (.barrierArrival 0 (2*step+1)),.ordinary (.barrierReturn 0 (2*step+1))] := by
  let g := current cfg ctx oracle r step
  let p := AmpereTiledLoop.pointersAt (AmpereTiledEntry.loopConfig cfg ctx) step
  have hg : g.groups = step := state_groups cfg ctx oracle r step
  have hc : g.copies.length = 3*step := state_copy_count cfg ctx oracle r step
  have hb : Ptx.Event.generation g.scalar.core 0 = 2*step := state_generation cfg ctx oracle r step
  have hp : Ptx.Event.generation (AmpereTiledStage.afterMma ctx oracle g p (r.payload step) (r.a step) (r.b step)).scalar.core 0 = 2*step+1 := by
    change Ptx.Event.generation (CopyStage.prepared ctx g p (r.payload step)).scalar.core 0 = _
    rw [CopyStage.prepared_generation,hb]
  change CopyStage.events ctx g p (r.payload step) ++
    MmaBlock.readEvents ctx (AmpereTiledAddresses.la ctx) (AmpereTiledAddresses.lb ctx) (r.a step) (r.b step) ++
    [.mmaEntry (callAt cfg ctx oracle r step),.mmaReturn (callAt cfg ctx oracle r step)] ++
    [.ordinary (.barrierArrival 0 (Ptx.Event.generation (AmpereTiledStage.afterMma ctx oracle g p (r.payload step) (r.a step) (r.b step)).scalar.core 0)),
     .ordinary (.barrierReturn 0 (Ptx.Event.generation (AmpereTiledStage.afterMma ctx oracle g p (r.payload step) (r.a step) (r.b step)).scalar.core 0))] = _
  simp only [CopyStage.events,hg,hc,hb,hp,List.append_assoc]
  rfl

theorem phase_length (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    (stepEvents cfg ctx oracle r step).length = 17 := rfl
theorem prefix_length (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (step : Nat) :
    (eventsThrough cfg ctx oracle r step).length = 17*step := by
  induction step with
  | zero => rfl
  | succ step ih => simp [eventsThrough,List.length_append,phase_length,ih,Nat.mul_add]
theorem events_length (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) :
    (events cfg ctx oracle r).length = 17*(cfg.k/16)+4 := by
  simp [events,prefix_length,AmpereTiledFinish.events]

theorem prefix_event (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle)
    (count phase slot : Nat) (hp : phase < count) (hs : slot < 17) :
    (eventsThrough cfg ctx oracle r count)[17*phase+slot]? = (stepEvents cfg ctx oracle r phase)[slot]? := by
  induction count with
  | zero => omega
  | succ count ih =>
    by_cases he : phase < count
    · rw [eventsThrough,List.getElem?_append_left (by rw [prefix_length]; omega)]
      exact ih he
    · have hh : phase = count := by omega
      subst phase
      rw [eventsThrough,List.getElem?_append_right (by rw [prefix_length]; omega),prefix_length]
      simp

theorem phase_event (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle)
    (phase slot : Nat) (hp : phase < cfg.k/16) (hs : slot < 17) :
    (events cfg ctx oracle r)[17*phase+slot]? = (stepEvents cfg ctx oracle r phase)[slot]? := by
  rw [events,List.getElem?_append_left (by rw [prefix_length]; omega)]
  exact prefix_event cfg ctx oracle r _ phase slot hp hs

theorem output_event (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (slot : Nat) :
    (events cfg ctx oracle r)[17*(cfg.k/16)+slot]? =
      (AmpereTiledFinish.events (AmpereTiledAddresses.c cfg ctx) (AmpereTiledAddresses.ch cfg ctx) (cValues oracle (cfg.k/16)))[slot]? := by
  rw [events,List.getElem?_append_right (by rw [prefix_length]; omega),prefix_length]
  simp

end
end Ptx.AmpereTiledEvents
