import Ptx.Kernels.AmpereTiledFragmentInputs
import Ptx.Kernels.AmpereTiledOutputAccesses

/-! Parameterized induction over every K phase and all actual source threads.
Memory agreement determines packed A/B inputs; mandatory full-warp arithmetic
determines returned accumulators. No output-value oracle is assumed correct. -/
namespace Ptx.AmpereTiledAccumulation
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledGraph Ptx.AmpereTiledEvents
open Ptx.AmpereTiledFragmentInputs
noncomputable section

def Invariant {cfg launch candidate} (h : SourceInfo cfg launch candidate) (a b : Matrix) (phase : Nat) : Prop :=
  ∀ t, ∀ ht : t ∈ candidate.traces, ∀ slot,
    cValues t.oracle phase slot = Mma.gatherC (tileC a b t.id.cta.y t.id.cta.x phase)
      (lane t.id (by simpa only [h.geometry] using (h.formed.2.2.1 t ht).1),slot)

theorem initial {cfg launch candidate} (h : SourceInfo cfg launch candidate) (a b : Matrix) : Invariant h a b 0 := by
  intro t ht slot
  simp [cValues,Mma.gatherC,tileC,partialProduct,product]

theorem entry_accumulator {cfg launch candidate a b event call phase} (h : SourceInfo cfg launch candidate)
    (hinv : Invariant h a b phase) (he : candidate.eventAt event = some (.mmaEntry call))
    (hp : call.ordinal = phase) (slot : Fin 4) :
    call.inputs.c slot = Mma.gatherC (tileC a b event.thread.cta.y event.thread.cta.x phase) (call.lane,slot) := by
  obtain ⟨t,ht,hid,hc,hl⟩ := entry_c h he
  rw [hc,hp,hinv t ht slot,hl,← hid]

theorem next {cfg launch candidate rf co a b phase} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hi : Input cfg a b launch.initial)
    (hmm : MmaConditions AmpereTiledGraph.code launch candidate) (hp : phase < cfg.k/16) (hinv : Invariant h a b phase) :
    Invariant h a b (phase+1) := by
  intro t ht slot
  obtain ⟨r,_,_,hevents⟩ := trace_view h ht
  have he : candidate.eventAt ⟨t.id,17*phase+14⟩ = some (.mmaReturn (callAt cfg (context launch t.id) t.oracle r phase)) := by
    rw [member_event h ht,hevents,phase_event _ _ _ _ phase 14 hp (by decide),phase_events]
    rfl
  have hordinal := call_ordinal cfg (context launch t.id) t.oracle r phase
  have hv : (context launch t.id).id.Valid (geometry cfg) := by simpa only [context,h.geometry] using (h.formed.2.2.1 t ht).1
  have hblock : (context launch t.id).block = (geometry cfg).block := congrArg Geometry.block h.geometry
  have hout := AmpereTiledMma.matched_accumulation_step hmm he a b t.id.cta.y t.id.cta.x phase
    (fun entry other hg reg => by
      have hvalue := entry_a h hm hi hg.2.2.2.2 reg
      have ho : other.ordinal = phase := hg.2.2.1.trans hordinal
      simpa only [ho,congrArg Dim3.y hg.1] using hvalue)
    (fun entry other hg reg => by
      have hvalue := entry_b h hm hi hg.2.2.2.2 reg
      have ho : other.ordinal = phase := hg.2.2.1.trans hordinal
      simpa only [ho,congrArg Dim3.x hg.1] using hvalue)
    (fun entry other hg reg => by
      have hvalue := entry_accumulator h hinv hg.2.2.2.2 (hg.2.2.1.trans hordinal) reg
      simpa only [congrArg Dim3.y hg.1,congrArg Dim3.x hg.1] using hvalue) slot
  rw [call_output,call_lane _ _ r hv hblock] at hout
  have hc : cValues t.oracle (phase+1) slot = t.oracle.matrix (10*phase+9) slot := by
    simp [cValues,show 10*(phase+1)-1 = 10*phase+9 by omega]
  exact hc.trans hout

theorem all_phases {cfg launch candidate rf co a b} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hi : Input cfg a b launch.initial)
    (hmm : MmaConditions AmpereTiledGraph.code launch candidate) {phase : Nat} (hp : phase ≤ cfg.k/16) : Invariant h a b phase := by
  induction phase with
  | zero => exact initial h a b
  | succ phase ih => exact next h hm hi hmm (by omega) (ih (by omega))

theorem coordinates {cfg : Config} (id : ThreadId) (hv : id.Valid (geometry cfg)) (slot : Fin 4) :
    16*id.cta.y+(Mma.cCoord (lane id hv,slot)).1.val = AmpereTiledOutputLayout.row id slot ∧
    8*id.cta.x+(Mma.cCoord (lane id hv,slot)).2.val = AmpereTiledOutputLayout.col id slot := by
  simp [Mma.cCoord,lane,Tiled.lane_x,Tiled.lane_y,AmpereTiledOutputLayout.row,AmpereTiledOutputLayout.col,Nat.add_assoc]

theorem final_accumulator {cfg launch candidate rf co a b} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hi : Input cfg a b launch.initial)
    (hmm : MmaConditions AmpereTiledGraph.code launch candidate) {t : ThreadTrace} (ht : t ∈ candidate.traces) (slot : Fin 4) :
    cValues t.oracle (cfg.k/16) slot = product a b (AmpereTiledOutputLayout.row t.id slot)
      (AmpereTiledOutputLayout.col t.id slot) cfg.k := by
  have hv := all_phases h hm hi hmm (Nat.le_refl (cfg.k/16)) t ht slot
  dsimp only [Mma.gatherC,tileC] at hv
  have hc := coordinates t.id (by simpa only [h.geometry] using (h.formed.2.2.1 t ht).1) slot
  rw [hc.1,hc.2,full_product_from_tiles h.layout] at hv
  exact hv

theorem active_post {cfg launch candidate rf co o a b} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hi : Input cfg a b launch.initial)
    (hmm : MmaConditions AmpereTiledGraph.code launch candidate) (ho : ObserverConstraints candidate launch.initial rf co o)
    (hd : o.domain = domain cfg) : Post cfg a b launch.initial o.output := by
  constructor
  · intro row col hr hc
    obtain ⟨id,_,slot,t,ht,hid,hrow,hcol,hw⟩ := AmpereTiledOutputAccesses.every_output_word h hm ho hd hr hc
    have hvalue := final_accumulator h hm hi hmm ht slot
    rw [hid,hrow,hcol] at hvalue
    rw [hvalue] at hw
    exact hw
  · intro loc hl hn
    exact AmpereTiledObservation.frame h ho hd hl hn

end
end Ptx.AmpereTiledAccumulation
