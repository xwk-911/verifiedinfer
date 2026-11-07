import Ptx.Kernels.AmpereTiledControl
import Ptx.Ampere.SourceBoundary

/-! Actual source-PC matching for the two repeated barrier sites. Generation
parity distinguishes PC 64 from PC 72; no unique-static-site shortcut is used. -/
namespace Ptx.AmpereTiledBarrierSources
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledGraph Ptx.AmpereTiledEvents
noncomputable section

theorem barrier_prefix {cfg : Config} (h : Layout cfg) (ctx : Scalar.Context) (oracle : Oracle)
    (r : ReplySet cfg ctx oracle) (hp : AmpereTiledInit.Params cfg ctx.params)
    (hv : ctx.id.Valid (geometry cfg)) (ha : Active cfg) {phase : Nat} (hphase : phase < cfg.k/16) (half : Fin 2) :
    ∃ before head, Ampere.run ctx oracle AmpereTiledGraph.code (64+21*phase+8*half.val) {} = .ok (before,head) ∧
      head.length = 17*phase+5+10*half.val ∧ before.scalar.core.thread.status = .running ∧
      before.scalar.core.thread.pc = 64+8*half.val ∧ Ptx.Event.generation before.scalar.core 0 = 2*phase+half.val := by
  let s := stateAt cfg ctx oracle r phase
  let g := current cfg ctx oracle r phase
  let p := AmpereTiledLoop.pointersAt (AmpereTiledEntry.loopConfig cfg ctx) phase
  have hi := state_invariant h ctx oracle r phase (by omega)
  have h32 : 16*(cfg.k/16) < 2^32 := by have hm := h.tiles.2.2; have hb := h.dimensions.2.2; omega
  have hg := AmpereTiledGuard.active ctx oracle s (16*phase) (16*(cfg.k/16)) hi.running hi.pc hi.index (hi.fixed 7) (by omega) h32
  have hstart : Ampere.run ctx oracle AmpereTiledGraph.code (59+21*phase) {} = .ok (g,eventsThrough cfg ctx oracle r phase) := by
    rw [show 59+21*phase = (57+21*phase)+2 by omega,Ampere.run_add,prefix_run h ctx oracle r hp hv ha phase (by omega)]
    simp only [Except.bind]
    rw [hg]
    simp only [Except.bind,List.append_nil]
    rfl
  have hnat (name : String) (hne : name ≠ "%p") : lookup name g.scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := by
    simp [g,current,s,AmpereTiledGuard.activeState,hne]
  have hsources (i : Fin 3) : lookup (CopyStage.sourceName i) g.scalar.core.thread.regs = some (CopyStage.source p i) := by
    rw [hnat _ (by fin_cases i <;> decide)]
    exact hi.sources i
  have hdestinations (i : Fin 3) : lookup (CopyStage.destinationName i) g.scalar.core.thread.regs = some (CopyStage.destination p i) := by
    rw [hnat _ (by fin_cases i <;> decide)]
    exact AmpereTiledLoop.destination_lookup hi i
  have hqa (i : Fin 3) : oracle.bytes (g.scalar.core.queries+i.val) = r.payload phase i := by
    simpa [g,current,AmpereTiledGuard.activeState,state_queries,AmpereTiledEntry.loopConfig] using r.bytes phase hphase i
  have hgr : g.scalar.core.thread.status = .running := by simpa [g,current,AmpereTiledGuard.activeState] using hi.running
  have hgg : Ptx.Event.generation g.scalar.core 0 = 2*phase := by
    change Ptx.Event.generation (stateAt cfg ctx oracle r phase).scalar.core 0 = _
    exact state_generation _ _ _ _ _
  fin_cases half
  · refine ⟨CopyStage.beforeBarrier ctx g p (r.payload phase),eventsThrough cfg ctx oracle r phase++(CopyStage.events ctx g p (r.payload phase)).take 5,?_,?_,?_,?_,?_⟩
    · have hcopy := CopyStage.execute_prefix AmpereTiledStage.copy_fragment ctx oracle g p (r.payload phase) hgr rfl hsources hdestinations (r.size phase hphase) hqa
      rw [show 64+21*phase+8*0 = (59+21*phase)+5 by omega,Ampere.run_add,hstart]
      simp only [Except.bind]
      rw [hcopy]
    · simp [prefix_length,CopyStage.events]
    · simpa only [CopyStage.before_barrier_status] using hgr
    · simp [g,current,AmpereTiledGuard.activeState]
    · simpa only [CopyStage.before_barrier_generation,Nat.add_zero] using hgg
  · have hfa (i : Fin 4) : declarationLookup (MmaBlock.accumulators.get i) g.scalar.floats = some (.f32,cValues oracle phase i) := by
      exact (AmpereTiledGuard.active_float s _ (by fin_cases i <;> decide) (hi.noInteger i)).trans (state_accumulators _ _ _ _ _ i)
    have hni (i : Fin 4) : lookup (MmaBlock.accumulators.get i) g.scalar.core.thread.regs = none := by
      rw [hnat _ (by fin_cases i <;> decide)]
      exact hi.noInteger i
    have hstage := AmpereTiledStage.execute_prefix ctx oracle g p (r.payload phase)
      (AmpereTiledAddresses.la ctx) (AmpereTiledAddresses.lb ctx) (r.a phase) (r.b phase) (cValues oracle phase) hgr rfl hsources hdestinations
      (by rw [hnat _ (by decide)]; exact hi.fixed 3) (by rw [hnat _ (by decide)]; exact hi.fixed 4) hfa hni (r.size phase hphase) hqa
      (by simpa [g,current,AmpereTiledGuard.activeState,state_queries,AmpereTiledEntry.loopConfig] using r.wordA phase hphase)
      (by simpa [g,current,AmpereTiledGuard.activeState,state_queries,AmpereTiledEntry.loopConfig] using r.wordB phase hphase)
    refine ⟨AmpereTiledStage.afterMma ctx oracle g p (r.payload phase) (r.a phase) (r.b phase),
      eventsThrough cfg ctx oracle r phase++(AmpereTiledStage.events ctx oracle g p (r.payload phase)
        (AmpereTiledAddresses.la ctx) (AmpereTiledAddresses.lb ctx) (r.a phase) (r.b phase) (cValues oracle phase)).take 15,?_,?_,?_,?_,?_⟩
    · rw [show 64+21*phase+8*1 = (59+21*phase)+13 by omega,Ampere.run_add,hstart]
      simp only [Except.bind]
      rw [hstage]
    · simp [prefix_length,AmpereTiledStage.events,CopyStage.events,MmaBlock.readEvents]
    · simpa only [AmpereTiledStage.after_mma_status] using hgr
    · rw [AmpereTiledStage.after_mma_pc]
      rfl
    · rw [AmpereTiledStage.after_mma_generation,hgg]

theorem barrier_pc {cfg launch candidate} (h : SourceInfo cfg launch candidate) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase : Nat} (hp : phase < cfg.k/16) (half offset : Fin 2) :
    sourcePC candidate AmpereTiledGraph.code launch.params launch.geometry.block
      ⟨id,17*phase+5+10*half.val+offset.val⟩ = some (64+8*half.val) := by
  obtain ⟨t,ht,hid⟩ := h.formed.2.2.2 id hv
  subst id
  obtain ⟨r,hcount,_,_⟩ := trace_view h ht
  have hv' : (context launch t.id).id.Valid (geometry cfg) := by simpa only [context,h.geometry] using hv
  obtain ⟨before,head,hprefix,hlen,hr,hpc,hgen⟩ := barrier_prefix h.layout (context launch t.id) t.oracle r h.params hv' h.active hp half
  have hstep := barrier_step (ctx := context launch t.id) (oracle := t.oracle) (code := AmpereTiledGraph.code) hr
    (show (AmpereTiledGraph.code)[before.scalar.core.thread.pc]? = some (.scalar (.integer (.barrier 0))) by rw [hpc]; fin_cases half <;> rfl)
  have he : [Event.ordinary (.barrierArrival 0 (Ptx.Event.generation before.scalar.core 0)),
      .ordinary (.barrierReturn 0 (Ptx.Event.generation before.scalar.core 0))][offset.val]? =
      some (if offset.val = 0 then .ordinary (.barrierArrival 0 (Ptx.Event.generation before.scalar.core 0)) else
        .ordinary (.barrierReturn 0 (Ptx.Event.generation before.scalar.core 0))) := by fin_cases offset <;> rfl
  have hs := source_pc_of_prefix h.formed ht hprefix hstep
    (by rw [hcount]; have hh := half.isLt; omega) he
  simpa only [hlen,hpc] using hs

theorem aligned {cfg launch candidate} (h : SourceInfo cfg launch candidate) : SourceAligned AmpereTiledGraph.code launch candidate := by
  rintro a b ⟨_,bid,generation,ha,hb⟩
  obtain ⟨pa,hpa,ia,_,hga,hsa⟩ := AmpereTiledControl.arrival_info h ha
  obtain ⟨pb,hpb,ib,_,hgb,hsb⟩ := AmpereTiledControl.return_info h hb
  have heq : ia = ib := Fin.ext (by have hi := ia.isLt; have hj := ib.isLt; omega)
  have aid : a = ⟨a.thread,17*pa+5+10*ia.val+0⟩ := by
    cases a
    simp only [Ptx.Event.EventId.mk.injEq,true_and]
    dsimp only at hsa
    omega
  have bid : b = ⟨b.thread,17*pb+5+10*ib.val+1⟩ := by
    cases b
    simp only [Ptx.Event.EventId.mk.injEq,true_and]
    dsimp only at hsb
    omega
  have hapc := barrier_pc h (AmpereTiledControl.event_owner_valid h ha) hpa ia 0
  have hbpc := barrier_pc h (AmpereTiledControl.event_owner_valid h hb) hpb ib 1
  refine ⟨64+8*ia.val,?_,?_⟩
  · change sourcePC candidate AmpereTiledGraph.code launch.params launch.geometry.block ⟨a.thread,17*pa+5+10*ia.val+0⟩ = _ at hapc
    rw [← aid] at hapc
    exact hapc
  · change sourcePC candidate AmpereTiledGraph.code launch.params launch.geometry.block ⟨b.thread,17*pb+5+10*ib.val+1⟩ = _ at hbpc
    rw [← bid] at hbpc
    simpa only [heq] using hbpc

end
end Ptx.AmpereTiledBarrierSources
