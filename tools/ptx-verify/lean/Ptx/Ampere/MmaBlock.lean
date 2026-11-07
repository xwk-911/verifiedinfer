import Ptx.Ampere.Updates
import Ptx.Ampere.Trace
import Mathlib.Tactic.NormNum

/-! Relocatable execution of the actual six packed shared loads and MMA slot.
The state may have arbitrary unrelated bindings and prior copy/group history.
Read answers and returned arithmetic values remain independent here. Global
memory agreement and full-warp matching are separate proof obligations. -/
namespace Ptx.Ampere.MmaBlock
open Ptx.ISA
noncomputable section

structure Fragment (code : List Instr) (base : Nat) : Prop where
  load0 : code[base+0]? = some (.loadWord32 .shared "%ra0" {base := .reg "%la",offset := 0})
  load1 : code[base+1]? = some (.loadWord32 .shared "%ra1" {base := .reg "%la",offset := 256})
  load2 : code[base+2]? = some (.loadWord32 .shared "%ra2" {base := .reg "%la",offset := 16})
  load3 : code[base+3]? = some (.loadWord32 .shared "%ra3" {base := .reg "%la",offset := 272})
  load4 : code[base+4]? = some (.loadWord32 .shared "%rb0" {base := .reg "%lb",offset := 0})
  load5 : code[base+5]? = some (.loadWord32 .shared "%rb1" {base := .reg "%lb",offset := 16})
  mma : code[base+6]? = some (.mma ⟨"%acc0","%acc1","%acc2","%acc3"⟩
    ⟨"%ra0","%ra1","%ra2","%ra3"⟩ ⟨"%rb0","%rb1"⟩ ⟨"%acc0","%acc1","%acc2","%acc3"⟩)

def accumulators : Registers4 := ⟨"%acc0","%acc1","%acc2","%acc3"⟩
def aRegisters : Registers4 := ⟨"%ra0","%ra1","%ra2","%ra3"⟩
def bRegisters : Registers2 := ⟨"%rb0","%rb1"⟩
def inputs (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (acc : Fin 4 → ℝ) : MmaInputs := {
  a := fun i => if i.val = 0 then a 0 else if i.val = 1 then a 1 else if i.val = 2 then a 2 else a 3
  b := fun i => if i.val = 0 then b 0 else b 1
  c := fun i => if i.val = 0 then acc 0 else if i.val = 1 then acc 1 else if i.val = 2 then acc 2 else acc 3
}
def loaded (s : State) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) : State :=
  wordAction (wordAction (wordAction (wordAction (wordAction (wordAction s
    "%ra0" (.packed (a 0))) "%ra1" (.packed (a 1))) "%ra2" (.packed (a 2)))
    "%ra3" (.packed (a 3))) "%rb0" (.packed (b 0))) "%rb1" (.packed (b 1))
def readEvents (ctx : Scalar.Context) (pa pb : Nat) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) : List Event := [
  .ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+0)⟩ (a 0).encode),
  .ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+256)⟩ (a 1).encode),
  .ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+16)⟩ (a 2).encode),
  .ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+272)⟩ (a 3).encode),
  .ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pb+0)⟩ (b 0).encode),
  .ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pb+16)⟩ (b 1).encode)
 ]

theorem execute {code : List Instr} {base : Nat} (hf : Fragment code base)
    (ctx : Scalar.Context) (oracle : Oracle) (s : State) (pa pb : Nat)
    (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (acc : Fin 4 → ℝ)
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = base)
    (ha : lookup "%la" s.scalar.core.thread.regs = some pa)
    (hb : lookup "%lb" s.scalar.core.thread.regs = some pb)
    (hc : ∀ i, declarationLookup (accumulators.get i) s.scalar.floats = some (.f32,acc i))
    (hqa : ∀ i, oracle.word32 (s.scalar.core.queries+i.val) = .packed (a i))
    (hqb : ∀ i, oracle.word32 (s.scalar.core.queries+4+i.val) = .packed (b i)) :
    let output := oracle.matrix (s.scalar.core.queries+6)
    let call := makeMmaCall ctx (loaded s a b) (inputs a b acc) output
    run ctx oracle code 7 s = .ok (mmaAction (loaded s a b) accumulators output,
      readEvents ctx pa pb a b ++ [.mmaEntry call,.mmaReturn call]) := by
  let s1 := wordAction s "%ra0" (.packed (a 0))
  let s2 := wordAction s1 "%ra1" (.packed (a 1))
  let s3 := wordAction s2 "%ra2" (.packed (a 2))
  let s4 := wordAction s3 "%ra3" (.packed (a 3))
  let s5 := wordAction s4 "%rb0" (.packed (b 0))
  let s6 := wordAction s5 "%rb1" (.packed (b 1))
  have hc0 := hc (0 : Fin 4)
  have hc1 := hc (1 : Fin 4)
  have hc2 := hc (2 : Fin 4)
  have hc3 := hc (3 : Fin 4)
  dsimp [accumulators,Registers4.get] at hc0 hc1 hc2 hc3
  have h0 : step ctx oracle code s =
      .ok (s1,[.ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+0)⟩ (a 0).encode)]) := by
    have hh := word_step (ctx := ctx) (oracle := oracle) (code := code) (s := s)
      (space := .shared) (dst := "%ra0") (address := {base := .reg "%la",offset := 0})
      (by simpa [hr,hp,Nat.add_assoc] using hr)
      (by simpa [hr,hp,Nat.add_assoc] using hf.load0)
      (show evalAddr ctx.id.tid.x s.scalar.core.thread {base := .reg "%la",offset := 0} = .ok (wrap 64 (pa+0)) by
        simp [evalAddr,Ptx.eval,ha,hb,bind,Except.bind,pure,Except.pure])
    have hq := hqa (0 : Fin 4)
    norm_num at hq
    simpa [s1,hr,hp,Nat.add_assoc,hq,Location.resolve,Word32.encode] using hh
  have h1 : step ctx oracle code s1 =
      .ok (s2,[.ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+256)⟩ (a 1).encode)]) := by
    have hh := word_step (ctx := ctx) (oracle := oracle) (code := code) (s := s1)
      (space := .shared) (dst := "%ra1") (address := {base := .reg "%la",offset := 256})
      (by simpa [s1,hr,hp,Nat.add_assoc] using hr)
      (by simpa [s1,hr,hp,Nat.add_assoc] using hf.load1)
      (show evalAddr ctx.id.tid.x s1.scalar.core.thread {base := .reg "%la",offset := 256} = .ok (wrap 64 (pa+256)) by
        simp [evalAddr,Ptx.eval,s1,ha,hb,bind,Except.bind,pure,Except.pure])
    have hq := hqa (1 : Fin 4)
    norm_num at hq
    simpa [s2,s1,hr,hp,Nat.add_assoc,hq,Location.resolve,Word32.encode] using hh
  have h2 : step ctx oracle code s2 =
      .ok (s3,[.ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+16)⟩ (a 2).encode)]) := by
    have hh := word_step (ctx := ctx) (oracle := oracle) (code := code) (s := s2)
      (space := .shared) (dst := "%ra2") (address := {base := .reg "%la",offset := 16})
      (by simpa [s2,s1,hr,hp,Nat.add_assoc] using hr)
      (by simpa [s2,s1,hr,hp,Nat.add_assoc] using hf.load2)
      (show evalAddr ctx.id.tid.x s2.scalar.core.thread {base := .reg "%la",offset := 16} = .ok (wrap 64 (pa+16)) by
        simp [evalAddr,Ptx.eval,s2,s1,ha,hb,bind,Except.bind,pure,Except.pure])
    have hq := hqa (2 : Fin 4)
    norm_num at hq
    simpa [s3,s2,s1,hr,hp,Nat.add_assoc,hq,Location.resolve,Word32.encode] using hh
  have h3 : step ctx oracle code s3 =
      .ok (s4,[.ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pa+272)⟩ (a 3).encode)]) := by
    have hh := word_step (ctx := ctx) (oracle := oracle) (code := code) (s := s3)
      (space := .shared) (dst := "%ra3") (address := {base := .reg "%la",offset := 272})
      (by simpa [s3,s2,s1,hr,hp,Nat.add_assoc] using hr)
      (by simpa [s3,s2,s1,hr,hp,Nat.add_assoc] using hf.load3)
      (show evalAddr ctx.id.tid.x s3.scalar.core.thread {base := .reg "%la",offset := 272} = .ok (wrap 64 (pa+272)) by
        simp [evalAddr,Ptx.eval,s3,s2,s1,ha,hb,bind,Except.bind,pure,Except.pure])
    have hq := hqa (3 : Fin 4)
    norm_num at hq
    simpa [s4,s3,s2,s1,hr,hp,Nat.add_assoc,hq,Location.resolve,Word32.encode] using hh
  have h4 : step ctx oracle code s4 =
      .ok (s5,[.ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pb+0)⟩ (b 0).encode)]) := by
    have hh := word_step (ctx := ctx) (oracle := oracle) (code := code) (s := s4)
      (space := .shared) (dst := "%rb0") (address := {base := .reg "%lb",offset := 0})
      (by simpa [s4,s3,s2,s1,hr,hp,Nat.add_assoc] using hr)
      (by simpa [s4,s3,s2,s1,hr,hp,Nat.add_assoc] using hf.load4)
      (show evalAddr ctx.id.tid.x s4.scalar.core.thread {base := .reg "%lb",offset := 0} = .ok (wrap 64 (pb+0)) by
        simp [evalAddr,Ptx.eval,s4,s3,s2,s1,ha,hb,bind,Except.bind,pure,Except.pure])
    have hq := hqb (0 : Fin 2)
    norm_num at hq
    simpa [s5,s4,s3,s2,s1,hr,hp,Nat.add_assoc,hq,Location.resolve,Word32.encode] using hh
  have h5 : step ctx oracle code s5 =
      .ok (s6,[.ordinary (.read ⟨.shared ctx.id.cta,wrap 64 (pb+16)⟩ (b 1).encode)]) := by
    have hh := word_step (ctx := ctx) (oracle := oracle) (code := code) (s := s5)
      (space := .shared) (dst := "%rb1") (address := {base := .reg "%lb",offset := 16})
      (by simpa [s5,s4,s3,s2,s1,hr,hp,Nat.add_assoc] using hr)
      (by simpa [s5,s4,s3,s2,s1,hr,hp,Nat.add_assoc] using hf.load5)
      (show evalAddr ctx.id.tid.x s5.scalar.core.thread {base := .reg "%lb",offset := 16} = .ok (wrap 64 (pb+16)) by
        simp [evalAddr,Ptx.eval,s5,s4,s3,s2,s1,ha,hb,bind,Except.bind,pure,Except.pure])
    have hq := hqb (1 : Fin 2)
    norm_num at hq
    simpa [s6,s5,s4,s3,s2,s1,hr,hp,Nat.add_assoc,hq,Location.resolve,Word32.encode] using hh
  have hin : readMmaInputs s6 aRegisters bRegisters accumulators = .ok (inputs a b acc) := by
    simp [readMmaInputs,requirePacked,Scalar.eval,Scalar.require,liftScalar,
      s6,s5,s4,s3,s2,s1,aRegisters,bRegisters,accumulators,Registers4.get,
      hc0,hc1,hc2,hc3,inputs,bind,Except.bind,pure,Except.pure]
  have h6 := mma_step (ctx := ctx) (oracle := oracle) (code := code) (s := s6)
    (d := accumulators) (a := aRegisters) (b := bRegisters) (c := accumulators)
    (by simpa [s6,s5,s4,s3,s2,s1] using hr)
    (by simpa [s6,s5,s4,s3,s2,s1,hp,Nat.add_assoc,accumulators,aRegisters,bRegisters] using hf.mma)
    (by decide) hin
  simp [run,h0,h1,h2,h3,h4,h5,h6,Except.bind,loaded,readEvents,
    s6,s5,s4,s3,s2,s1,Nat.add_assoc]

@[simp] theorem loaded_pc (s : State) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (loaded s a b).scalar.core.thread.pc = s.scalar.core.thread.pc+6 := by simp [loaded,Nat.add_assoc]
@[simp] theorem loaded_queries (s : State) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (loaded s a b).scalar.core.queries = s.scalar.core.queries+6 := by simp [loaded,Nat.add_assoc]
@[simp] theorem loaded_status (s : State) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (loaded s a b).scalar.core.thread.status = s.scalar.core.thread.status := rfl
@[simp] theorem loaded_copies (s : State) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (loaded s a b).copies = s.copies := rfl
@[simp] theorem loaded_groups (s : State) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (loaded s a b).groups = s.groups := rfl
@[simp] theorem loaded_mma_calls (s : State) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) :
    (loaded s a b).mmaCalls = s.mmaCalls := rfl

theorem inputs_a (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (acc : Fin 4 → ℝ) : (inputs a b acc).a = a := by
  funext i
  fin_cases i <;> rfl

theorem inputs_b (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (acc : Fin 4 → ℝ) : (inputs a b acc).b = b := by
  funext i
  fin_cases i <;> rfl

theorem inputs_c (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (acc : Fin 4 → ℝ) : (inputs a b acc).c = acc := by
  funext i
  fin_cases i <;> rfl

theorem final_accumulator (s : State) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (output : Fin 4 → ℝ) (i : Fin 4) :
    Scalar.eval .f32 (mmaAction (loaded s a b) accumulators output).scalar (.reg (accumulators.get i)) = .ok (output i) := by
  fin_cases i <;> simp [Scalar.eval,Scalar.require,mmaAction,accumulators,Registers4.get,declarationLookup,
    bind,Except.bind,pure,Except.pure]

theorem final_float (s : State) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (output : Fin 4 → ℝ) (i : Fin 4) :
    declarationLookup (accumulators.get i) (mmaAction (loaded s a b) accumulators output).scalar.floats = some (.f32,output i) := by
  fin_cases i <;> simp [mmaAction,accumulators,Registers4.get,declarationLookup]

theorem final_nat (s : State) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (output : Fin 4 → ℝ) (i : Fin 4) :
    lookup (accumulators.get i) (mmaAction (loaded s a b) accumulators output).scalar.core.thread.regs = none := by
  rw [mma_nat]
  fin_cases i <;> simp [accumulators,Registers4.get,Registers4.names]

theorem loaded_nat_frame (s : State) (a : Fin 4 → PackedF16) (b : Fin 2 → PackedF16) (name : String)
    (ha : ∀ i, name ≠ aRegisters.get i) (hb : ∀ i, name ≠ bRegisters.get i) :
    lookup name (loaded s a b).scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have ha3 := ha 3
  have hb0 := hb 0
  have hb1 := hb 1
  dsimp [aRegisters,bRegisters,Registers4.get,Registers2.get] at ha0 ha1 ha2 ha3 hb0 hb1
  simp [loaded,ha0,ha1,ha2,ha3,hb0,hb1]

end
end Ptx.Ampere.MmaBlock
