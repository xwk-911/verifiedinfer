import Ptx.Kernels.AmpereTiledEntry
import Ptx.Kernels.AmpereTiledGeometry

/-! Complete PC-zero source executions and count reconstruction. Active reply
sizes/tags still require extraction from arbitrary complete source candidates;
there is no memory/warp admission or output-value assumption here. -/
namespace Ptx.AmpereTiledSource
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec
noncomputable section
abbrev code := Generated.ampere_tiled_matmul.program

theorem active_run {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg)
    (replies : AmpereTiledLoop.Replies (AmpereTiledEntry.loopConfig cfg ctx) oracle) :
    ∃ last emitted, Ampere.run ctx oracle code (64+21*(cfg.k/16)) {} = .ok (last,emitted) ∧
      last.scalar.core.thread.status = .done ∧ emitted.length = 17*(cfg.k/16)+4 ∧
      last.scalar.core.queries = 10*(cfg.k/16) := by
  have hg := AmpereTiledGeometry.active_guards h hv ha
  have hi := AmpereTiledEntry.invariant cfg ctx h.dimensions.2.2 h.tiles.2.2
  have hb : 16*(AmpereTiledEntry.loopConfig cfg ctx).tiles < 2^32 := by
    change 16*(cfg.k/16) < 2^32
    have hm := h.tiles.2.2
    have h32 := h.dimensions.2.2
    omega
  obtain ⟨last,emitted,hr,hd,he,hq⟩ := AmpereTiledLoop.run_to_completion ctx oracle replies hb (cfg.k/16)
    (by simp [AmpereTiledEntry.loopConfig]) hi
  refine ⟨last,emitted,?_,hd,he,?_⟩
  · rw [show 64+21*(cfg.k/16) = 57+(21*(cfg.k/16)+7) by omega,Ampere.run_add,
      AmpereTiledEntry.source_prefix cfg ctx oracle hp hg.1 hg.2]
    simp only [Except.bind,List.nil_append]
    rw [hr]
  · simpa [AmpereTiledEntry.loopConfig] using hq

theorem active_complete_counts {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg)
    (replies : AmpereTiledLoop.Replies (AmpereTiledEntry.loopConfig cfg ctx) oracle)
    {count last emitted} (hr : Ampere.run ctx oracle code count {} = .ok (last,emitted))
    (hd : last.scalar.core.thread.status = .done) :
    count = 64+21*(cfg.k/16) ∧ emitted.length = 17*(cfg.k/16)+4 ∧ last.scalar.core.queries = 10*(cfg.k/16) := by
  obtain ⟨final,events,hrun,hfinal,hlen,hq⟩ := active_run h ctx oracle hp hv ha replies
  obtain ⟨hc,hs,he⟩ := Ampere.complete_run_unique hr hd hrun hfinal
  exact ⟨hc,he ▸ hlen,hs ▸ hq⟩

theorem row_masked_run {cfg : Config} (ctx : Scalar.Context) (oracle : Oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hz : cfg.m = 0) :
    Ampere.run ctx oracle code 15 {} = .ok (AmpereTiledInit.maskedFinal cfg ctx,[]) := by
  have hg : wrap 32 cfg.m ≤ AmpereTiledInit.tileRow ctx := by simp [hz,wrap]
  rw [show 15 = 12+3 by decide,Ampere.run_add,AmpereTiledInit.indexed_run cfg ctx oracle hp]
  simp only [Except.bind,List.nil_append]
  rw [AmpereTiledInit.row_mask_run cfg ctx oracle hg]

theorem col_masked_run {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hv : ctx.id.Valid (geometry cfg))
    (hm : 0 < cfg.m) (hz : cfg.n = 0) :
    Ampere.run ctx oracle code 17 {} = .ok (AmpereTiledInit.maskedFinal cfg ctx,[]) := by
  have hr : AmpereTiledInit.tileRow ctx < wrap 32 cfg.m := by
    rw [(AmpereTiledGeometry.tile_rows h hv).1,
      show wrap 32 cfg.m = cfg.m from Nat.mod_eq_of_lt h.dimensions.1]
    exact AmpereTiledGeometry.tile_base_active (by decide) h.tiles.1 hv.1.2.1 hm
  have hc : wrap 32 cfg.n ≤ AmpereTiledInit.tileCol ctx := by simp [hz,wrap]
  rw [show 17 = 12+5 by decide,Ampere.run_add,AmpereTiledInit.indexed_run cfg ctx oracle hp]
  simp only [Except.bind,List.nil_append]
  rw [AmpereTiledInit.col_mask_run cfg ctx oracle hr hc]

theorem inactive_run {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hv : ctx.id.Valid (geometry cfg)) (ha : ¬ Active cfg) :
    ∃ last, Ampere.run ctx oracle code (if cfg.m = 0 then 15 else 17) {} = .ok (last,[]) ∧
      last.scalar.core.thread.status = .done ∧ last.scalar.core.queries = 0 := by
  by_cases hm : cfg.m = 0
  · refine ⟨AmpereTiledInit.maskedFinal cfg ctx,?_,rfl,rfl⟩
    simpa only [hm,ite_true] using row_masked_run ctx oracle hp hm
  · have hm' : 0 < cfg.m := by omega
    have hn : cfg.n = 0 := by by_contra hn; exact ha ⟨hm',by omega⟩
    refine ⟨AmpereTiledInit.maskedFinal cfg ctx,?_,rfl,rfl⟩
    simpa only [hm,ite_false] using col_masked_run h ctx oracle hp hv hm' hn

/-- Zero K does not inspect any copy/word/MMA oracle answer. -/
theorem zero_k_events {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) (hz : cfg.k = 0) :
    let entry := AmpereTiledEntry.ready cfg ctx
    let ex := AmpereTiledGuard.exitState entry
    Ampere.run ctx oracle code 64 {} = .ok (AmpereTiledFinish.finalState ex,
      AmpereTiledFinish.events (AmpereTiledAddresses.c cfg ctx) (AmpereTiledAddresses.ch cfg ctx) (fun _ => 0)) := by
  let entry := AmpereTiledEntry.ready cfg ctx
  let ex := AmpereTiledGuard.exitState entry
  have hi := AmpereTiledEntry.invariant cfg ctx h.dimensions.2.2 h.tiles.2.2
  have hn (name : String) (hne : name ≠ "%p") : lookup name ex.scalar.core.thread.regs = lookup name entry.scalar.core.thread.regs := by
    simp [ex,AmpereTiledGuard.exitState,hne]
  have hf (i : Fin 4) : declarationLookup (MmaBlock.accumulators.get i) ex.scalar.floats = some (.f32,0) := by
    have hne : MmaBlock.accumulators.get i ≠ "%p" := by fin_cases i <;> decide
    have hni : lookup (MmaBlock.accumulators.get i) entry.scalar.core.thread.regs = none := hi.noInteger i
    have hfi : declarationLookup (MmaBlock.accumulators.get i) entry.scalar.floats = some (.f32,0) :=
      AmpereTiledEntry.zeroed_accumulator (AmpereTiledAddresses.shared cfg ctx) i
    simpa [ex,AmpereTiledGuard.exitState,Ampere.intPC,Ampere.intAssign,hne,hni] using hfi
  have hguard := AmpereTiledGuard.exit ctx oracle entry 0 hi.running hi.pc hi.index
    (by simpa [entry,AmpereTiledEntry.loopConfig,AmpereTiledLoop.fixedName,AmpereTiledLoop.fixedValue,hz] using hi.fixed 7) (by decide)
  have hfinish := AmpereTiledFinish.execute ctx oracle ex (AmpereTiledAddresses.c cfg ctx) (AmpereTiledAddresses.ch cfg ctx) (fun _ => 0)
    (by simpa [ex,AmpereTiledGuard.exitState] using hi.running) rfl
    (by rw [hn "%c" (by decide)]; exact hi.fixed 5)
    (by rw [hn "%ch" (by decide)]; exact hi.fixed 6) hf
  have hg := AmpereTiledGeometry.active_guards h hv ha
  rw [show 64 = 57+7 by decide,Ampere.run_add,AmpereTiledEntry.source_prefix cfg ctx oracle hp hg.1 hg.2]
  simp only [Except.bind,List.nil_append]
  rw [show 7 = 2+5 by decide,Ampere.run_add,hguard]
  simp only [Except.bind,List.nil_append]
  rw [hfinish]

theorem zero_k_complete_counts {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle)
    (hp : AmpereTiledInit.Params cfg ctx.params) (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) (hz : cfg.k = 0)
    {count last emitted} (hr : Ampere.run ctx oracle code count {} = .ok (last,emitted))
    (hd : last.scalar.core.thread.status = .done) : count = 64 ∧ emitted.length = 4 ∧ last.scalar.core.queries = 0 := by
  have hs := zero_k_events h ctx oracle hp hv ha hz
  obtain ⟨hc,hstate,hevents⟩ := Ampere.complete_run_unique hr hd hs rfl
  refine ⟨hc,?_,?_⟩
  · rw [hevents]
    rfl
  · rw [hstate]
    rfl

end
end Ptx.AmpereTiledSource
