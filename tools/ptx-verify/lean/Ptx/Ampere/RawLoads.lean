import Ptx.Ampere.Inversion
import Ptx.Ampere.MmaBlock

/-! Six actual word loads with arbitrary reply variants. Packed types are
derived later from a successful actual MMA, rather than assumed at the loads. -/
namespace Ptx.Ampere.RawLoads
open Ptx.ISA
noncomputable section

def aWords (oracle : Oracle) (query : Nat) (i : Fin 4) : Word32 := oracle.word32 (query+i.val)
def bWords (oracle : Oracle) (query : Nat) (i : Fin 2) : Word32 := oracle.word32 (query+4+i.val)
def loaded (s : State) (a : Fin 4 → Word32) (b : Fin 2 → Word32) : State :=
  wordAction (wordAction (wordAction (wordAction (wordAction (wordAction s
    "%ra0" (a 0)) "%ra1" (a 1)) "%ra2" (a 2)) "%ra3" (a 3)) "%rb0" (b 0)) "%rb1" (b 1)
def events (ctx : Scalar.Context) (pa pb : Nat) (a : Fin 4 → Word32) (b : Fin 2 → Word32) : List Event := [
  .ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+0)⟩ (a 0).encode),
  .ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+256)⟩ (a 1).encode),
  .ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+16)⟩ (a 2).encode),
  .ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+272)⟩ (a 3).encode),
  .ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pb+0)⟩ (b 0).encode),
  .ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pb+16)⟩ (b 1).encode)]

@[simp] theorem loaded_pc (s : State) (a : Fin 4 → Word32) (b : Fin 2 → Word32) :
    (loaded s a b).scalar.core.thread.pc = s.scalar.core.thread.pc+6 := by simp [loaded,Nat.add_assoc]
@[simp] theorem loaded_queries (s : State) (a : Fin 4 → Word32) (b : Fin 2 → Word32) :
    (loaded s a b).scalar.core.queries = s.scalar.core.queries+6 := by simp [loaded,Nat.add_assoc]
@[simp] theorem loaded_status (s : State) (a : Fin 4 → Word32) (b : Fin 2 → Word32) :
    (loaded s a b).scalar.core.thread.status = s.scalar.core.thread.status := by simp [loaded]

theorem loaded_a (s : State) (a : Fin 4 → Word32) (b : Fin 2 → Word32) (i : Fin 4) :
    declarationLookup (MmaBlock.aRegisters.get i) (loaded s a b).packed = (a i).packedValue := by
  fin_cases i <;> simp [loaded,MmaBlock.aRegisters,Registers4.get]
theorem loaded_b (s : State) (a : Fin 4 → Word32) (b : Fin 2 → Word32) (i : Fin 2) :
    declarationLookup (MmaBlock.bRegisters.get i) (loaded s a b).packed = (b i).packedValue := by
  fin_cases i <;> simp [loaded,MmaBlock.bRegisters,Registers2.get]

theorem execute {code : List Instr} {base : Nat} (hf : MmaBlock.Fragment code base)
    (ctx : Scalar.Context) (oracle : Oracle) (s : State) (pa pb : Nat)
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = base)
    (ha : lookup "%la" s.scalar.core.thread.regs = some pa)
    (hb : lookup "%lb" s.scalar.core.thread.regs = some pb) :
    run ctx oracle code 6 s = .ok (loaded s (aWords oracle s.scalar.core.queries) (bWords oracle s.scalar.core.queries),
      events ctx pa pb (aWords oracle s.scalar.core.queries) (bWords oracle s.scalar.core.queries)) := by
  let aw := aWords oracle s.scalar.core.queries
  let bw := bWords oracle s.scalar.core.queries
  let s1 := wordAction s "%ra0" (aw 0)
  let s2 := wordAction s1 "%ra1" (aw 1)
  let s3 := wordAction s2 "%ra2" (aw 2)
  let s4 := wordAction s3 "%ra3" (aw 3)
  let s5 := wordAction s4 "%rb0" (bw 0)
  let s6 := wordAction s5 "%rb1" (bw 1)
  have h0 : step ctx oracle code s = .ok (s1,[.ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+0)⟩ (aw 0).encode)]) := by
    simpa [s1,aw,aWords,Location.resolve] using word_step (ctx := ctx) (oracle := oracle) (code := code) (s := s)
      hr (by simpa [hp] using hf.load0)
      (show evalAddr ctx.id.tid.x s.scalar.core.thread {base := .reg "%la",offset := 0} = .ok (wrap 64 (pa+0)) by
        simp [evalAddr,Ptx.eval,ha,bind,Except.bind,pure,Except.pure])
  have h1 : step ctx oracle code s1 = .ok (s2,[.ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+256)⟩ (aw 1).encode)]) := by
    simpa [s2,s1,aw,aWords,Location.resolve] using word_step (ctx := ctx) (oracle := oracle) (code := code) (s := s1)
      (by simpa [s1] using hr) (by simpa [s1,hp] using hf.load1)
      (show evalAddr ctx.id.tid.x s1.scalar.core.thread {base := .reg "%la",offset := 256} = .ok (wrap 64 (pa+256)) by
        simp [evalAddr,Ptx.eval,s1,word_action_nat_frame,ha,bind,Except.bind,pure,Except.pure])
  have h2 : step ctx oracle code s2 = .ok (s3,[.ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+16)⟩ (aw 2).encode)]) := by
    simpa [s3,s2,s1,aw,aWords,Nat.add_assoc,Location.resolve] using word_step (ctx := ctx) (oracle := oracle) (code := code) (s := s2)
      (by simpa [s2,s1] using hr) (by simpa [s2,s1,hp,Nat.add_assoc] using hf.load2)
      (show evalAddr ctx.id.tid.x s2.scalar.core.thread {base := .reg "%la",offset := 16} = .ok (wrap 64 (pa+16)) by
        simp [evalAddr,Ptx.eval,s2,s1,word_action_nat_frame,ha,bind,Except.bind,pure,Except.pure])
  have h3 : step ctx oracle code s3 = .ok (s4,[.ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+272)⟩ (aw 3).encode)]) := by
    simpa [s4,s3,s2,s1,aw,aWords,Nat.add_assoc,Location.resolve] using word_step (ctx := ctx) (oracle := oracle) (code := code) (s := s3)
      (by simpa [s3,s2,s1] using hr) (by simpa [s3,s2,s1,hp,Nat.add_assoc] using hf.load3)
      (show evalAddr ctx.id.tid.x s3.scalar.core.thread {base := .reg "%la",offset := 272} = .ok (wrap 64 (pa+272)) by
        simp [evalAddr,Ptx.eval,s3,s2,s1,word_action_nat_frame,ha,bind,Except.bind,pure,Except.pure])
  have h4 : step ctx oracle code s4 = .ok (s5,[.ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pb+0)⟩ (bw 0).encode)]) := by
    simpa [s5,s4,s3,s2,s1,aw,bw,aWords,bWords,Nat.add_assoc,Location.resolve] using word_step (ctx := ctx) (oracle := oracle) (code := code) (s := s4)
      (by simpa [s4,s3,s2,s1] using hr) (by simpa [s4,s3,s2,s1,hp,Nat.add_assoc] using hf.load4)
      (show evalAddr ctx.id.tid.x s4.scalar.core.thread {base := .reg "%lb",offset := 0} = .ok (wrap 64 (pb+0)) by
        simp [evalAddr,Ptx.eval,s4,s3,s2,s1,word_action_nat_frame,hb,bind,Except.bind,pure,Except.pure])
  have h5 : step ctx oracle code s5 = .ok (s6,[.ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pb+16)⟩ (bw 1).encode)]) := by
    simpa [s6,s5,s4,s3,s2,s1,aw,bw,aWords,bWords,Nat.add_assoc,Location.resolve] using word_step (ctx := ctx) (oracle := oracle) (code := code) (s := s5)
      (by simpa [s5,s4,s3,s2,s1] using hr) (by simpa [s5,s4,s3,s2,s1,hp,Nat.add_assoc] using hf.load5)
      (show evalAddr ctx.id.tid.x s5.scalar.core.thread {base := .reg "%lb",offset := 16} = .ok (wrap 64 (pb+16)) by
        simp [evalAddr,Ptx.eval,s5,s4,s3,s2,s1,word_action_nat_frame,hb,bind,Except.bind,pure,Except.pure])
  simp only [run,h0,h1,h2,h3,h4,h5,Except.bind]
  simp [loaded,events,s6,s5,s4,s3,s2,s1,aw,bw]

theorem packed_of_mma {code : List Instr} {base : Nat} (hf : MmaBlock.Fragment code base)
    {ctx oracle s pa pb count last emitted}
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = base)
    (ha : lookup "%la" s.scalar.core.thread.regs = some pa)
    (hb : lookup "%lb" s.scalar.core.thread.regs = some pb)
    (hc : run ctx oracle code count s = .ok (last,emitted)) (hd : last.scalar.core.thread.status = .done) :
    (∀ i : Fin 4, ∃ pair, oracle.word32 (s.scalar.core.queries+i.val) = .packed pair) ∧
      (∀ i : Fin 2, ∃ pair, oracle.word32 (s.scalar.core.queries+4+i.val) = .packed pair) := by
  have hload := execute hf ctx oracle s pa pb hr hp ha hb
  obtain ⟨next,more,hstep⟩ := step_after_running_prefix hc hd hload (by simpa using hr)
  obtain ⟨inputs,hin⟩ := mma_inputs_of_step (by simpa using hr)
    (by simpa [hp] using hf.mma) hstep
  have hm := read_mma_packed hin
  constructor
  · intro i
    obtain ⟨pair,he⟩ := hm.1 i
    change declarationLookup (MmaBlock.aRegisters.get i) (loaded s (aWords oracle s.scalar.core.queries) (bWords oracle s.scalar.core.queries)).packed = some pair at he
    rw [loaded_a] at he
    change (oracle.word32 (s.scalar.core.queries+i.val)).packedValue = some pair at he
    cases hq : oracle.word32 (s.scalar.core.queries+i.val) with
    | integer n => simp [hq,Word32.packedValue] at he
    | packed p => exact ⟨p,rfl⟩
  · intro i
    obtain ⟨pair,he⟩ := hm.2 i
    change declarationLookup (MmaBlock.bRegisters.get i) (loaded s (aWords oracle s.scalar.core.queries) (bWords oracle s.scalar.core.queries)).packed = some pair at he
    rw [loaded_b] at he
    change (oracle.word32 (s.scalar.core.queries+4+i.val)).packedValue = some pair at he
    cases hq : oracle.word32 (s.scalar.core.queries+4+i.val) with
    | integer n => simp [hq,Word32.packedValue] at he
    | packed p => exact ⟨p,rfl⟩

end
end Ptx.Ampere.RawLoads
