import Ptx.Kernels.AmpereTiledEvents

/-! Exhaustive inventories of canonical source events for arbitrary K. Since
every actual completed source has this trace, no read/write event is omitted.
Memory values, phase order and launch admission are separate obligations. -/
namespace Ptx.AmpereTiledInventory
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledEvents
noncomputable section

def readBase (ctx : Scalar.Context) (i : Fin 6) : Location := ⟨.shared ctx.id.cta,
  if i.val < 4 then wrap 64 (AmpereTiledAddresses.la ctx+256*(i.val%2)+16*(i.val/2))
  else wrap 64 (AmpereTiledAddresses.lb ctx+16*(i.val-4))⟩
def readPair {cfg ctx oracle} (r : ReplySet cfg ctx oracle) (phase : Nat) (i : Fin 6) : PackedF16 :=
  if i.val < 4 then r.a phase ⟨i.val%4,by omega⟩ else r.b phase ⟨(i.val-4)%2,by omega⟩
def writeBase (cfg : Config) (ctx : Scalar.Context) (i : Fin 4) : Location := ⟨.global,
  if i.val < 2 then wrap 64 (AmpereTiledAddresses.c cfg ctx+4*i.val)
  else wrap 64 (AmpereTiledAddresses.ch cfg ctx+4*(i.val-2))⟩
def writeBytes (cfg : Config) (oracle : Oracle) (i : Fin 4) : List Symbolic.Byte :=
  Symbolic.encode .f32 (cValues oracle (cfg.k/16) i)

theorem phase_issue (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle)
    (phase : Nat) (i : Fin 3) :
    (stepEvents cfg ctx oracle r phase)[i.val]? = some (.issue (3*phase+i.val) (operationAt cfg ctx oracle r phase i)) := by
  rw [phase_events]
  fin_cases i <;> rfl
theorem phase_read (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (r : ReplySet cfg ctx oracle)
    (phase : Nat) (i : Fin 6) :
    (stepEvents cfg ctx oracle r phase)[7+i.val]? = some (.ordinary (.read (readBase ctx i) (readPair r phase i).encode)) := by
  rw [phase_events]
  fin_cases i <;> rfl
theorem finish_write (cfg : Config) (ctx : Scalar.Context) (oracle : Oracle) (i : Fin 4) :
    (AmpereTiledFinish.events (AmpereTiledAddresses.c cfg ctx) (AmpereTiledAddresses.ch cfg ctx) (cValues oracle (cfg.k/16)))[i.val]? =
      some (.ordinary (.write (writeBase cfg ctx i) (writeBytes cfg oracle i))) := by
  fin_cases i <;> rfl

theorem event_cases {cfg ctx oracle} {r : ReplySet cfg ctx oracle} {serial event}
    (he : (events cfg ctx oracle r)[serial]? = some event) :
    (∃ phase, phase < cfg.k/16 ∧ ∃ slot : Fin 17, serial = 17*phase+slot.val ∧
      (stepEvents cfg ctx oracle r phase)[slot.val]? = some event) ∨
    (∃ slot : Fin 4, serial = 17*(cfg.k/16)+slot.val ∧
      (AmpereTiledFinish.events (AmpereTiledAddresses.c cfg ctx) (AmpereTiledAddresses.ch cfg ctx) (cValues oracle (cfg.k/16)))[slot.val]? = some event) := by
  have hb := (List.getElem?_eq_some_iff.mp he).1
  rw [events_length] at hb
  by_cases hp : serial < 17*(cfg.k/16)
  · have hphase : serial/17 < cfg.k/16 := by omega
    have hslot : serial%17 < 17 := Nat.mod_lt _ (by decide)
    have hi : serial = 17*(serial/17)+serial%17 := by omega
    refine .inl ⟨serial/17,hphase,⟨serial%17,hslot⟩,hi,?_⟩
    rw [hi,phase_event cfg ctx oracle r _ _ hphase hslot] at he
    exact he
  · have hslot : serial-17*(cfg.k/16) < 4 := by omega
    have hi : serial = 17*(cfg.k/16)+(serial-17*(cfg.k/16)) := by omega
    refine .inr ⟨⟨serial-17*(cfg.k/16),hslot⟩,hi,?_⟩
    rw [hi,output_event] at he
    exact he

theorem issue_cases {cfg ctx oracle} {r : ReplySet cfg ctx oracle} {serial ordinal op}
    (he : (events cfg ctx oracle r)[serial]? = some (.issue ordinal op)) :
    ∃ phase, phase < cfg.k/16 ∧ ∃ part : Fin 3,
      ordinal = 3*phase+part.val ∧ serial = 17*phase+part.val ∧ op = operationAt cfg ctx oracle r phase part := by
  rcases event_cases he with ⟨phase,hp,slot,hserial,hslot⟩ | ⟨slot,_,hslot⟩
  · rw [phase_events] at hslot
    fin_cases slot <;> simp [MmaBlock.readEvents] at hslot
    · obtain ⟨rfl,rfl⟩ := hslot
      exact ⟨phase,hp,0,rfl,hserial,rfl⟩
    · obtain ⟨rfl,rfl⟩ := hslot
      exact ⟨phase,hp,1,rfl,hserial,rfl⟩
    · obtain ⟨rfl,rfl⟩ := hslot
      exact ⟨phase,hp,2,rfl,hserial,rfl⟩
  · fin_cases slot <;> simp [AmpereTiledFinish.events] at hslot

theorem read_cases {cfg ctx oracle} {r : ReplySet cfg ctx oracle} {serial base bytes}
    (he : (events cfg ctx oracle r)[serial]? = some (.ordinary (.read base bytes))) :
    ∃ phase, phase < cfg.k/16 ∧ ∃ reg : Fin 6,
      serial = 17*phase+7+reg.val ∧ base = readBase ctx reg ∧ bytes = (readPair r phase reg).encode := by
  rcases event_cases he with ⟨phase,hp,slot,hserial,hslot⟩ | ⟨slot,_,hslot⟩
  · have hrange : 7 ≤ slot.val ∧ slot.val < 13 := by
      rw [phase_events] at hslot
      fin_cases slot <;> simp [MmaBlock.readEvents] at hslot <;> decide
    let reg : Fin 6 := ⟨slot.val-7,by omega⟩
    have hs : slot.val = 7+reg.val := by dsimp [reg]; omega
    rw [hs,phase_read] at hslot
    have hh : readBase ctx reg = base ∧ (readPair r phase reg).encode = bytes := by simpa using hslot
    exact ⟨phase,hp,reg,by omega,hh.1.symm,hh.2.symm⟩
  · fin_cases slot <;> simp [AmpereTiledFinish.events] at hslot

theorem write_cases {cfg ctx oracle} {r : ReplySet cfg ctx oracle} {serial base bytes}
    (he : (events cfg ctx oracle r)[serial]? = some (.ordinary (.write base bytes))) :
    ∃ slot : Fin 4, serial = 17*(cfg.k/16)+slot.val ∧ base = writeBase cfg ctx slot ∧ bytes = writeBytes cfg oracle slot := by
  rcases event_cases he with ⟨phase,_,slot,_,hslot⟩ | ⟨slot,hserial,hslot⟩
  · rw [phase_events] at hslot
    fin_cases slot <;> simp [MmaBlock.readEvents] at hslot
  · rw [finish_write] at hslot
    have hh : writeBase cfg ctx slot = base ∧ writeBytes cfg oracle slot = bytes := by simpa using hslot
    exact ⟨slot,hserial,hh.1.symm,hh.2.symm⟩

theorem mma_return_cases {cfg ctx oracle} {r : ReplySet cfg ctx oracle} {serial call}
    (he : (events cfg ctx oracle r)[serial]? = some (.mmaReturn call)) :
    ∃ phase, phase < cfg.k/16 ∧ serial = 17*phase+14 ∧ call = callAt cfg ctx oracle r phase := by
  rcases event_cases he with ⟨phase,hp,slot,hserial,hslot⟩ | ⟨slot,_,hslot⟩
  · rw [phase_events] at hslot
    fin_cases slot <;> simp [MmaBlock.readEvents] at hslot
    subst call
    exact ⟨phase,hp,hserial,rfl⟩
  · fin_cases slot <;> simp [AmpereTiledFinish.events] at hslot

theorem mma_entry_cases {cfg ctx oracle} {r : ReplySet cfg ctx oracle} {serial call}
    (he : (events cfg ctx oracle r)[serial]? = some (.mmaEntry call)) :
    ∃ phase, phase < cfg.k/16 ∧ serial = 17*phase+13 ∧ call = callAt cfg ctx oracle r phase := by
  rcases event_cases he with ⟨phase,hp,slot,hserial,hslot⟩ | ⟨slot,_,hslot⟩
  · rw [phase_events] at hslot
    fin_cases slot <;> simp [MmaBlock.readEvents] at hslot
    subst call
    exact ⟨phase,hp,hserial,rfl⟩
  · fin_cases slot <;> simp [AmpereTiledFinish.events] at hslot

theorem wait_cases {cfg ctx oracle} {r : ReplySet cfg ctx oracle} {serial groups keep}
    (he : (events cfg ctx oracle r)[serial]? = some (.wait groups keep)) :
    ∃ phase, phase < cfg.k/16 ∧ serial = 17*phase+4 ∧ groups = phase+1 ∧ keep = 0 := by
  rcases event_cases he with ⟨phase,hp,slot,hserial,hslot⟩ | ⟨slot,_,hslot⟩
  · rw [phase_events] at hslot
    fin_cases slot <;> simp [MmaBlock.readEvents] at hslot
    obtain ⟨rfl,rfl⟩ := hslot
    exact ⟨phase,hp,hserial,rfl,rfl⟩
  · fin_cases slot <;> simp [AmpereTiledFinish.events] at hslot

theorem barrier_arrival_cases {cfg ctx oracle} {r : ReplySet cfg ctx oracle} {serial bid generation}
    (he : (events cfg ctx oracle r)[serial]? = some (.ordinary (.barrierArrival bid generation))) :
    ∃ phase, phase < cfg.k/16 ∧ ∃ half : Fin 2,
      bid = 0 ∧ generation = 2*phase+half.val ∧ serial = 17*phase+5+10*half.val := by
  rcases event_cases he with ⟨phase,hp,slot,hserial,hslot⟩ | ⟨slot,_,hslot⟩
  · rw [phase_events] at hslot
    fin_cases slot <;> simp [MmaBlock.readEvents] at hslot
    · obtain ⟨rfl,rfl⟩ := hslot
      exact ⟨phase,hp,0,rfl,rfl,hserial⟩
    · obtain ⟨rfl,rfl⟩ := hslot
      exact ⟨phase,hp,1,rfl,rfl,hserial⟩
  · fin_cases slot <;> simp [AmpereTiledFinish.events] at hslot

theorem barrier_return_cases {cfg ctx oracle} {r : ReplySet cfg ctx oracle} {serial bid generation}
    (he : (events cfg ctx oracle r)[serial]? = some (.ordinary (.barrierReturn bid generation))) :
    ∃ phase, phase < cfg.k/16 ∧ ∃ half : Fin 2,
      bid = 0 ∧ generation = 2*phase+half.val ∧ serial = 17*phase+6+10*half.val := by
  rcases event_cases he with ⟨phase,hp,slot,hserial,hslot⟩ | ⟨slot,_,hslot⟩
  · rw [phase_events] at hslot
    fin_cases slot <;> simp [MmaBlock.readEvents] at hslot
    · obtain ⟨rfl,rfl⟩ := hslot
      exact ⟨phase,hp,0,rfl,rfl,hserial⟩
    · obtain ⟨rfl,rfl⟩ := hslot
      exact ⟨phase,hp,1,rfl,rfl,hserial⟩
  · fin_cases slot <;> simp [AmpereTiledFinish.events] at hslot

theorem no_rmw {cfg ctx oracle} {r : ReplySet cfg ctx oracle} {serial : Nat} {scope base bytes} :
    (events cfg ctx oracle r)[serial]? ≠ some (Ampere.Event.ordinary (.rmw scope base bytes)) := by
  intro he
  rcases event_cases he with ⟨phase,_,slot,_,hslot⟩ | ⟨slot,_,hslot⟩
  · rw [phase_events] at hslot
    fin_cases slot <;> simp [MmaBlock.readEvents] at hslot
  · fin_cases slot <;> simp [AmpereTiledFinish.events] at hslot

end
end Ptx.AmpereTiledInventory
