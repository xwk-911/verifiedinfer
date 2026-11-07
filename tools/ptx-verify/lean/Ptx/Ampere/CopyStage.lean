import Ptx.Ampere.Rules
import Ptx.Ampere.ScalarSteps
import Ptx.Ampere.Trace
import Mathlib.Tactic.NormNum

/-! Relocatable execution of three independent 8-byte copies, commit, wait and
CTA barrier. Payloads and prior history are arbitrary. This is local source
execution; neither visibility to a peer nor payload correctness is assumed. -/
namespace Ptx.Ampere.CopyStage
open Ptx.ISA
noncomputable section

structure Pointers where
  a : Nat
  ah : Nat
  b : Nat
  sa : Nat
  sah : Nat
  sb : Nat

def sourceName (i : Fin 3) : String := if i.val = 0 then "%a" else if i.val = 1 then "%ah" else "%b"
def destinationName (i : Fin 3) : String := if i.val = 0 then "%sa" else if i.val = 1 then "%sah" else "%sb"
def source (p : Pointers) (i : Fin 3) : Nat := if i.val = 0 then p.a else if i.val = 1 then p.ah else p.b
def destination (p : Pointers) (i : Fin 3) : Nat := if i.val = 0 then p.sa else if i.val = 1 then p.sah else p.sb

structure Fragment (code : List Instr) (base : Nat) : Prop where
  copy0 : code[base+0]? = some (.copy .ca {base := .reg "%sa"} {base := .reg "%a"} 8)
  copy1 : code[base+1]? = some (.copy .ca {base := .reg "%sah"} {base := .reg "%ah"} 8)
  copy2 : code[base+2]? = some (.copy .ca {base := .reg "%sb"} {base := .reg "%b"} 8)
  commit : code[base+3]? = some .commit
  wait : code[base+4]? = some (.wait 0)
  barrier : code[base+5]? = some (.scalar (.integer (.barrier 0)))

def operation (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) (i : Fin 3) : Copy :=
  ⟨.ca,s.groups,⟨.global,wrap 64 (source p i)⟩,⟨.shared ctx.id.cta,wrap 64 (destination p i)⟩,payload i⟩
def issued (s : State) (op : Copy) : State := (issue s op).1

def beforeBarrier (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) : State :=
  let s1 := issued s (operation ctx s p payload 0)
  let s2 := issued s1 (operation ctx s p payload 1)
  let s3 := issued s2 (operation ctx s p payload 2)
  let s4 := {advance s3 with groups := s3.groups+1}
  advance s4

def prepared (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) : State :=
  let s1 := issued s (operation ctx s p payload 0)
  let s2 := issued s1 (operation ctx s p payload 1)
  let s3 := issued s2 (operation ctx s p payload 2)
  let s4 := {advance s3 with groups := s3.groups+1}
  barrierState (advance s4) 0

def events (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) : List Event := [
  .issue s.copies.length (operation ctx s p payload 0),
  .issue (s.copies.length+1) (operation ctx s p payload 1),
  .issue (s.copies.length+2) (operation ctx s p payload 2),
  .commit s.groups,.wait (s.groups+1) 0,
  .ordinary (.barrierArrival 0 (Ptx.Event.generation s.scalar.core 0)),
  .ordinary (.barrierReturn 0 (Ptx.Event.generation s.scalar.core 0))]

theorem execute_prefix {code : List Instr} {base : Nat} (hf : Fragment code base)
    (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte)
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = base)
    (hs : ∀ i, lookup (sourceName i) s.scalar.core.thread.regs = some (source p i))
    (hd : ∀ i, lookup (destinationName i) s.scalar.core.thread.regs = some (destination p i))
    (hsize : ∀ i, (payload i).length = 8)
    (hq : ∀ i, oracle.bytes (s.scalar.core.queries+i.val) = payload i) :
    run ctx oracle code 5 s = .ok (beforeBarrier ctx s p payload,(events ctx s p payload).take 5) := by
  let s1 := issued s (operation ctx s p payload 0)
  let s2 := issued s1 (operation ctx s p payload 1)
  let s3 := issued s2 (operation ctx s p payload 2)
  let s4 := {advance s3 with groups := s3.groups+1}
  let s5 := advance s4
  have hsrc0 := hs (0 : Fin 3)
  have hdst0 := hd (0 : Fin 3)
  have hq0 := hq (0 : Fin 3)
  norm_num [sourceName,destinationName,source,destination] at hsrc0 hdst0 hq0
  have h0 : step ctx oracle code s = .ok (s1,[.issue (s.copies.length+0) (operation ctx s p payload 0)]) := by
    have hh := copy_step (ctx := ctx) (oracle := oracle) (code := code) (s := s)
      (cache := .ca) (dst := {base := .reg "%sa"}) (src := {base := .reg "%a"})
      (size := 8) (srcAddr := wrap 64 (source p 0)) (dstAddr := wrap 64 (destination p 0))
      (by simp [issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc])
      (by simpa [issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc] using hf.copy0) (by decide)
      (by simp [evalAddr,Ptx.eval,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc,hsrc0,source,bind,Except.bind,pure,Except.pure])
      (by simp [evalAddr,Ptx.eval,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc,hdst0,destination,bind,Except.bind,pure,Except.pure])
      (by simpa [issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc,hq0] using hsize (0 : Fin 3))
    simpa [s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc,operation,hq0,source,destination] using hh
  have hsrc1 := hs (1 : Fin 3)
  have hdst1 := hd (1 : Fin 3)
  have hq1 := hq (1 : Fin 3)
  norm_num [sourceName,destinationName,source,destination] at hsrc1 hdst1 hq1
  have h1 : step ctx oracle code s1 = .ok (s2,[.issue (s.copies.length+1) (operation ctx s p payload 1)]) := by
    have hh := copy_step (ctx := ctx) (oracle := oracle) (code := code) (s := s1)
      (cache := .ca) (dst := {base := .reg "%sah"}) (src := {base := .reg "%ah"})
      (size := 8) (srcAddr := wrap 64 (source p 1)) (dstAddr := wrap 64 (destination p 1))
      (by simp [s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc])
      (by simpa [s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc] using hf.copy1) (by decide)
      (by simp [evalAddr,Ptx.eval,s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc,hsrc1,source,bind,Except.bind,pure,Except.pure])
      (by simp [evalAddr,Ptx.eval,s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc,hdst1,destination,bind,Except.bind,pure,Except.pure])
      (by simpa [s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc,hq1] using hsize (1 : Fin 3))
    simpa [s2,s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc,operation,hq1,source,destination] using hh
  have hsrc2 := hs (2 : Fin 3)
  have hdst2 := hd (2 : Fin 3)
  have hq2 := hq (2 : Fin 3)
  norm_num [sourceName,destinationName,source,destination] at hsrc2 hdst2 hq2
  have h2 : step ctx oracle code s2 = .ok (s3,[.issue (s.copies.length+2) (operation ctx s p payload 2)]) := by
    have hh := copy_step (ctx := ctx) (oracle := oracle) (code := code) (s := s2)
      (cache := .ca) (dst := {base := .reg "%sb"}) (src := {base := .reg "%b"})
      (size := 8) (srcAddr := wrap 64 (source p 2)) (dstAddr := wrap 64 (destination p 2))
      (by simp [s2,s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc])
      (by simpa [s2,s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc] using hf.copy2) (by decide)
      (by simp [evalAddr,Ptx.eval,s2,s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc,hsrc2,source,bind,Except.bind,pure,Except.pure])
      (by simp [evalAddr,Ptx.eval,s2,s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc,hdst2,destination,bind,Except.bind,pure,Except.pure])
      (by simpa [s2,s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc,hq2] using hsize (2 : Fin 3))
    simpa [s3,s2,s1,issued,issue,advance,Ptx.advance,hr,hp,Nat.add_assoc,operation,hq2,source,destination] using hh
  have h3 : step ctx oracle code s3 = .ok (s4,[.commit s.groups]) := by
    simpa [s4,s3,s2,s1,issued,issue,advance] using
      (commit_step (ctx := ctx) (oracle := oracle) (code := code) (s := s3)
        (by simp [s3,s2,s1,issued,issue,advance,Ptx.advance,hr])
        (by simpa [s3,s2,s1,issued,issue,advance,Ptx.advance,hp,Nat.add_assoc] using hf.commit))
  have h4 : step ctx oracle code s4 = .ok (s5,[.wait (s.groups+1) 0]) := by
    simpa [s5,s4,s3,s2,s1,issued,issue,advance] using
      (wait_step (ctx := ctx) (oracle := oracle) (code := code) (s := s4)
        (by simp [s4,s3,s2,s1,issued,issue,advance,Ptx.advance,hr])
        (by simpa [s4,s3,s2,s1,issued,issue,advance,Ptx.advance,hp,Nat.add_assoc] using hf.wait) (by decide))
  simp only [run,h0,h1,h2,h3,h4,Except.bind,List.append_assoc,List.nil_append]
  simp [beforeBarrier,events,s5,s4,s3,s2,s1,issued,issue,advance,Nat.add_assoc]

theorem execute {code : List Instr} {base : Nat} (hf : Fragment code base)
    (ctx : Scalar.Context) (oracle : Oracle) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte)
    (hr : s.scalar.core.thread.status = .running) (hp : s.scalar.core.thread.pc = base)
    (hs : ∀ i, lookup (sourceName i) s.scalar.core.thread.regs = some (source p i))
    (hd : ∀ i, lookup (destinationName i) s.scalar.core.thread.regs = some (destination p i))
    (hsize : ∀ i, (payload i).length = 8)
    (hq : ∀ i, oracle.bytes (s.scalar.core.queries+i.val) = payload i) :
    run ctx oracle code 6 s = .ok (prepared ctx s p payload,events ctx s p payload) := by
  have hprefix := execute_prefix hf ctx oracle s p payload hr hp hs hd hsize hq
  have hbar := barrier_step (ctx := ctx) (oracle := oracle) (code := code) (s := beforeBarrier ctx s p payload)
    (by simpa [beforeBarrier,issued,issue,advance,Ptx.advance] using hr)
    (by simpa [beforeBarrier,issued,issue,advance,Ptx.advance,hp,Nat.add_assoc] using hf.barrier)
  rw [show 6 = 5+1 from rfl,run_add,hprefix]
  simp only [Except.bind,run,hbar,List.append_nil]
  rfl

@[simp] theorem before_barrier_pc (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) :
    (beforeBarrier ctx s p payload).scalar.core.thread.pc = s.scalar.core.thread.pc+5 := by
  simp [beforeBarrier,issued,issue,advance,Ptx.advance,Nat.add_assoc]
@[simp] theorem before_barrier_status (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) :
    (beforeBarrier ctx s p payload).scalar.core.thread.status = s.scalar.core.thread.status := rfl
@[simp] theorem before_barrier_generation (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) :
    Ptx.Event.generation (beforeBarrier ctx s p payload).scalar.core 0 = Ptx.Event.generation s.scalar.core 0 := rfl

@[simp] theorem prepared_pc (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) :
    (prepared ctx s p payload).scalar.core.thread.pc = s.scalar.core.thread.pc+6 := by
  simp [prepared,issued,issue,advance,Ptx.advance,Nat.add_assoc]
@[simp] theorem prepared_queries (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) :
    (prepared ctx s p payload).scalar.core.queries = s.scalar.core.queries+3 := by
  simp [prepared,issued,issue,advance,Nat.add_assoc]
@[simp] theorem prepared_status (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) :
    (prepared ctx s p payload).scalar.core.thread.status = s.scalar.core.thread.status := rfl
@[simp] theorem prepared_nat (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) (name : String) :
    lookup name (prepared ctx s p payload).scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := rfl

theorem prepared_float (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) (name : String)
    (hn : lookup name s.scalar.core.thread.regs = none) :
    declarationLookup name (prepared ctx s p payload).scalar.floats = declarationLookup name s.scalar.floats := by
  apply barrier_float
  exact hn

@[simp] theorem prepared_copies (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) :
    (prepared ctx s p payload).copies = s.copies ++
      [operation ctx s p payload 0,operation ctx s p payload 1,operation ctx s p payload 2] := by
  simp [prepared,barrierState,issued,issue,advance,List.append_assoc]
@[simp] theorem prepared_groups (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) :
    (prepared ctx s p payload).groups = s.groups+1 := rfl
@[simp] theorem prepared_mma_calls (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) :
    (prepared ctx s p payload).mmaCalls = s.mmaCalls := rfl
@[simp] theorem prepared_generation (ctx : Scalar.Context) (s : State) (p : Pointers) (payload : Fin 3 → List Symbolic.Byte) :
    Ptx.Event.generation (prepared ctx s p payload).scalar.core 0 = Ptx.Event.generation s.scalar.core 0+1 := by
  simp [prepared,issued,issue,advance,Ptx.Event.generation,barrierState,Scalar.finishInteger]

end
end Ptx.Ampere.CopyStage
