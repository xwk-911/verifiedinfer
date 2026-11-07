import Ptx.Kernels.AmpereTiledInputRead

/-! Actual six packed reads equal the independent matrix tile's A/B fragments.
Every premise is source provenance, original input representation or memory
admission; fragment values are conclusions rather than caller certificates. -/
namespace Ptx.AmpereTiledFragmentInputs
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledGraph Ptx.AmpereTiledEvents
open Ptx.AmpereTiledInputRead
noncomputable section

def lane {cfg : Config} (id : ThreadId) (hv : id.Valid (geometry cfg)) : Mma.Lane :=
  Tiled.lane ⟨id.tid.x,hv.2.1⟩ ⟨id.tid.y,hv.2.2.1⟩

theorem expected_a {cfg : Config} (a b : Matrix) (id : ThreadId) (hv : id.Valid (geometry cfg))
    (phase : Nat) (reg : Fin 4) (half : Fin 2) :
    expected a b id phase ⟨reg.val,by have hh := reg.isLt; omega⟩ half =
      (Mma.packA (Mma.gatherA (tileA a id.cta.y phase)) (lane id hv,reg)).half half := by
  fin_cases reg <;> fin_cases half <;>
    simp [expected,inputRow,inputK,Mma.packA,Mma.gatherA,tileA,lane,Mma.aCoord,Tiled.lane_x,Tiled.lane_y,PackedF16.half] <;>
    congr 1

theorem expected_b {cfg : Config} (a b : Matrix) (id : ThreadId) (hv : id.Valid (geometry cfg))
    (phase : Nat) (reg : Fin 2) (half : Fin 2) :
    expected a b id phase ⟨4+reg.val,by have hh := reg.isLt; omega⟩ half =
      (Mma.packB (Mma.gatherB (tileB b id.cta.x phase)) (lane id hv,reg)).half half := by
  fin_cases reg <;> fin_cases half <;>
    simp [expected,inputCol,inputK,Mma.packB,Mma.gatherB,tileB,lane,Mma.bCoord,Tiled.lane_x,Tiled.lane_y,PackedF16.half] <;>
    congr 1

theorem phase_half {cfg launch candidate rf co a b} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hi : Input cfg a b launch.initial)
    {t : ThreadTrace} (ht : t ∈ candidate.traces) (r : ReplySet cfg (context launch t.id) t.oracle)
    (he : t.events = events cfg (context launch t.id) t.oracle r) {phase : Nat} (hp : phase < cfg.k/16)
    (reg : Fin 6) (half : Fin 2) :
    (AmpereTiledInventory.readPair r phase reg).half half = expected a b t.id phase reg half := by
  apply packed_read_half h hm hi (h.formed.2.2.1 t ht).1 hp reg (half := half)
  rw [member_event h ht,he,show 17*phase+7+reg.val = 17*phase+(7+reg.val) by omega,
    phase_event _ _ _ _ phase (7+reg.val) hp (by have hh := reg.isLt; omega)]
  exact AmpereTiledInventory.phase_read _ _ _ r phase reg

theorem reply_a {cfg launch candidate rf co a b} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hi : Input cfg a b launch.initial)
    {t : ThreadTrace} (ht : t ∈ candidate.traces) (r : ReplySet cfg (context launch t.id) t.oracle)
    (he : t.events = events cfg (context launch t.id) t.oracle r) {phase : Nat} (hp : phase < cfg.k/16)
    (reg : Fin 4) : r.a phase reg = Mma.packA (Mma.gatherA (tileA a t.id.cta.y phase))
      (lane t.id (by simpa only [h.geometry] using (h.formed.2.2.1 t ht).1),reg) := by
  apply PackedF16.ext_half
  intro half
  have hh := phase_half h hm hi ht r he hp ⟨reg.val,by have hh := reg.isLt; omega⟩ half
  have hlt := reg.isLt
  rw [expected_a a b t.id (by simpa only [h.geometry] using (h.formed.2.2.1 t ht).1) phase reg half] at hh
  simpa [AmpereTiledInventory.readPair,Nat.mod_eq_of_lt hlt] using hh

theorem reply_b {cfg launch candidate rf co a b} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hi : Input cfg a b launch.initial)
    {t : ThreadTrace} (ht : t ∈ candidate.traces) (r : ReplySet cfg (context launch t.id) t.oracle)
    (he : t.events = events cfg (context launch t.id) t.oracle r) {phase : Nat} (hp : phase < cfg.k/16)
    (reg : Fin 2) : r.b phase reg = Mma.packB (Mma.gatherB (tileB b t.id.cta.x phase))
      (lane t.id (by simpa only [h.geometry] using (h.formed.2.2.1 t ht).1),reg) := by
  apply PackedF16.ext_half
  intro half
  have hh := phase_half h hm hi ht r he hp ⟨4+reg.val,by have hh := reg.isLt; omega⟩ half
  have hlt := reg.isLt
  rw [expected_b a b t.id (by simpa only [h.geometry] using (h.formed.2.2.1 t ht).1) phase reg half] at hh
  simpa [AmpereTiledInventory.readPair,Nat.mod_eq_of_lt hlt] using hh

theorem call_lane {cfg : Config} (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle)
    (hv : ctx.id.Valid (geometry cfg)) (hb : ctx.block = (geometry cfg).block) (phase : Nat) :
    (callAt cfg ctx oracle r phase).lane = lane ctx.id hv := by
  apply Fin.ext
  change linearThread ctx%32 = (lane ctx.id hv).val
  have hx : ctx.id.tid.x < 4 := hv.2.1
  have hy : ctx.id.tid.y < 8 := hv.2.2.1
  have hz : ctx.id.tid.z = 0 := by have hh : ctx.id.tid.z < 1 := hv.2.2.2; omega
  simp only [linearThread,hb,geometry,hz,Nat.mul_zero,Nat.add_zero,lane,Tiled.lane]
  omega

theorem call_a (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (phase : Nat) :
    (callAt cfg ctx oracle r phase).inputs.a = r.a phase := MmaBlock.inputs_a _ _ _
theorem call_b (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle) (phase : Nat) :
    (callAt cfg ctx oracle r phase).inputs.b = r.b phase := MmaBlock.inputs_b _ _ _

theorem entry_shape {cfg launch candidate event call} (h : SourceInfo cfg launch candidate)
    (he : candidate.eventAt event = some (.mmaEntry call)) :
    ∃ t ∈ candidate.traces, t.id = event.thread ∧ ∃ r : ReplySet cfg (context launch t.id) t.oracle,
      t.events = events cfg (context launch t.id) t.oracle r ∧ ∃ phase, phase < cfg.k/16 ∧
      event.serial = 17*phase+13 ∧ call = callAt cfg (context launch t.id) t.oracle r phase := by
  obtain ⟨t,ht,hid,hget⟩ := eventAt_trace he
  obtain ⟨r,_,_,hevents⟩ := trace_view h ht
  rw [hevents] at hget
  obtain ⟨phase,hp,hs,hcall⟩ := AmpereTiledInventory.mma_entry_cases hget
  exact ⟨t,ht,hid,r,hevents,phase,hp,hs,hcall⟩

theorem entry_a {cfg launch candidate rf co a b event call} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hi : Input cfg a b launch.initial)
    (he : candidate.eventAt event = some (.mmaEntry call)) (reg : Fin 4) :
    call.inputs.a reg = Mma.packA (Mma.gatherA (tileA a event.thread.cta.y call.ordinal)) (call.lane,reg) := by
  obtain ⟨t,ht,hid,r,hevents,phase,hp,_,hcall⟩ := entry_shape h he
  subst call
  have hv : (context launch t.id).id.Valid (geometry cfg) := by simpa only [context,h.geometry] using (h.formed.2.2.1 t ht).1
  have hb : (context launch t.id).block = (geometry cfg).block := congrArg Geometry.block h.geometry
  rw [call_a,call_ordinal,call_lane _ _ r hv hb,← hid]
  exact reply_a h hm hi ht r hevents hp reg

theorem entry_b {cfg launch candidate rf co a b event call} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (hi : Input cfg a b launch.initial)
    (he : candidate.eventAt event = some (.mmaEntry call)) (reg : Fin 2) :
    call.inputs.b reg = Mma.packB (Mma.gatherB (tileB b event.thread.cta.x call.ordinal)) (call.lane,reg) := by
  obtain ⟨t,ht,hid,r,hevents,phase,hp,_,hcall⟩ := entry_shape h he
  subst call
  have hv : (context launch t.id).id.Valid (geometry cfg) := by simpa only [context,h.geometry] using (h.formed.2.2.1 t ht).1
  have hb : (context launch t.id).block = (geometry cfg).block := congrArg Geometry.block h.geometry
  rw [call_b,call_ordinal,call_lane _ _ r hv hb,← hid]
  exact reply_b h hm hi ht r hevents hp reg

theorem entry_c {cfg launch candidate event call} (h : SourceInfo cfg launch candidate)
    (he : candidate.eventAt event = some (.mmaEntry call)) :
    ∃ t, ∃ ht : t ∈ candidate.traces, t.id = event.thread ∧ call.inputs.c = cValues t.oracle call.ordinal ∧
      call.lane = lane t.id (by simpa only [h.geometry] using (h.formed.2.2.1 t ht).1) := by
  obtain ⟨t,ht,hid,r,_,phase,_,_,hcall⟩ := entry_shape h he
  subst call
  exact ⟨t,ht,hid,by rw [call_old_c,call_ordinal],call_lane _ _ r
    (by simpa only [context,h.geometry] using (h.formed.2.2.1 t ht).1) (congrArg Geometry.block h.geometry) phase⟩

end
end Ptx.AmpereTiledFragmentInputs
