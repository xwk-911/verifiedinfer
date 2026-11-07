import Ptx.Generated.CpAsyncCopy
import Ptx.Ampere.Trace
import Ptx.Ampere.Rules
import Ptx.Scalar.IntegerMemory
import Mathlib.Tactic.NormNum

/-! Source execution of the actual sixteen-byte helper. Copy bytes and scalar
load replies remain independent here; memory agreement is a separate theorem.
The source has no loop, but reconstruction quantifies over arbitrary finite runs.
-/
namespace Ptx.CpAsyncCopyTrace
open Ptx.ISA Ptx.Ampere
noncomputable section
abbrev code := Generated.cp_async_copy.program
abbrev Answers := Fin 4 → Nat
def word (answers : Answers) (i : Fin 4) : Nat := wrap 32 (answers i)
def payload (answers : Answers) : List Symbolic.Byte :=
  Scalar.u32Bytes (word answers 0) ++ Scalar.u32Bytes (word answers 1) ++
  Scalar.u32Bytes (word answers 2) ++ Scalar.u32Bytes (word answers 3)
theorem payload_size (answers : Answers) : (payload answers).length = 16 := by
  simp [payload,Scalar.u32_bytes_size]

def operation (id : ThreadId) (src : Nat) (bytes : List Symbolic.Byte) : Copy :=
  ⟨.cg,0,⟨.global,src⟩,⟨.shared id.cta,0⟩,bytes⟩
def ready (src dst : Nat) : State := {
  scalar := {core := {thread := {pc := 2,regs := [("%y",dst),("%x",src)]}}}
}
def beforeRead (id : ThreadId) (src dst : Nat) (bytes : List Symbolic.Byte) : State := {
  scalar := {core := {thread := {pc := 6,regs := [("%y",dst),("%x",src)]},queries := 1,generations := [(0,1)]}}
  copies := [operation id src bytes]
  groups := 1
}

theorem parameters_run (ctx : Scalar.Context) (oracle : Ampere.Oracle) (src dst : Nat)
    (hx : lookup "X" ctx.params = some src) (hy : lookup "Y" ctx.params = some dst)
    (hs : src < 2^64) (hd : dst < 2^64) :
    Ampere.run ctx oracle code 2 {} = .ok (ready src dst,[]) := by
  have hsrc : wrap 64 src = src := Nat.mod_eq_of_lt hs
  have hdst : wrap 64 dst = dst := Nat.mod_eq_of_lt hd
  norm_num [Ampere.run,Ampere.step,code,Generated.cp_async_copy.program,ready,
    Ampere.scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
    Scalar.liftInteger,Scalar.finishInteger,Scalar.liftKind,Ptx.Event.step,localStep,
    Ampere.liftScalar,assign,Ptx.advance,put,lookup,hx,hy,hsrc,hdst,
    bind,Except.bind,pure,Except.pure]

theorem setup_run (ctx : Scalar.Context) (oracle : Ampere.Oracle) (src dst : Nat)
    (hs : src < 2^64) (hb : (oracle.bytes 0).length = 16) :
    Ampere.run ctx oracle code 4 (ready src dst) =
      .ok (beforeRead ctx.id src dst (oracle.bytes 0),
        [.issue 0 (operation ctx.id src (oracle.bytes 0)),.commit 0,.wait 1 0,
         .ordinary (.barrierArrival 0 0),.ordinary (.barrierReturn 0 0)]) := by
  have hsrc : wrap 64 src = src := Nat.mod_eq_of_lt hs
  norm_num [Ampere.run,Ampere.step,code,Generated.cp_async_copy.program,ready,beforeRead,operation,
    CopySize,Ampere.advance,Ampere.issue,Ampere.scalarSkeleton,Scalar.step,Scalar.require,
    Scalar.integer_delegate_fetch,Scalar.liftInteger,Scalar.finishInteger,Scalar.liftKind,
    Ptx.Event.step,Ptx.Event.generation,Ampere.liftScalar,Ampere.liftInteger,
    evalAddr,Ptx.eval,Ptx.advance,lookup,hsrc,hb,wrap,
    bind,Except.bind,pure,Except.pure]
  exact hs

def beforeRet (id : ThreadId) (src dst : Nat) (bytes : List Symbolic.Byte) (answers : Answers) : State := {
  scalar := {core := {thread := {pc := 14,regs := [("%v",word answers 3),("%y",dst),("%x",src)]},queries := 5,generations := [(0,1)]}}
  copies := [operation id src bytes]
  groups := 1
}
def finalState (id : ThreadId) (src dst : Nat) (bytes : List Symbolic.Byte) (answers : Answers) : State :=
  let before := beforeRet id src dst bytes answers
  {before with scalar := {before.scalar with core := {before.scalar.core with
    thread := {before.scalar.core.thread with status := .done}}}}
def dataEvents (id : ThreadId) (dst : Nat) (answers : Answers) : List Event := [
  .ordinary (.read ⟨.shared id.cta,0⟩ (Scalar.u32Bytes (word answers 0))),
  .ordinary (.write ⟨.global,dst⟩ (Scalar.u32Bytes (word answers 0))),
  .ordinary (.read ⟨.shared id.cta,4⟩ (Scalar.u32Bytes (word answers 1))),
  .ordinary (.write ⟨.global,dst+4⟩ (Scalar.u32Bytes (word answers 1))),
  .ordinary (.read ⟨.shared id.cta,8⟩ (Scalar.u32Bytes (word answers 2))),
  .ordinary (.write ⟨.global,dst+8⟩ (Scalar.u32Bytes (word answers 2))),
  .ordinary (.read ⟨.shared id.cta,12⟩ (Scalar.u32Bytes (word answers 3))),
  .ordinary (.write ⟨.global,dst+12⟩ (Scalar.u32Bytes (word answers 3)))]
def events (id : ThreadId) (src dst : Nat) (bytes : List Symbolic.Byte) (answers : Answers) : List Event :=
  [.issue 0 (operation id src bytes),.commit 0,.wait 1 0,
   .ordinary (.barrierArrival 0 0),.ordinary (.barrierReturn 0 0)] ++ dataEvents id dst answers

theorem data_run (ctx : Scalar.Context) (oracle : Ampere.Oracle) (src dst : Nat)
    (bytes : List Symbolic.Byte) (answers : Answers)
    (hd : dst+16 ≤ 2^64) (hq : ∀ i : Fin 4, oracle.scalar (1+i.val) = .integer (answers i)) :
    Ampere.run ctx oracle code 8 (beforeRead ctx.id src dst bytes) =
      .ok (beforeRet ctx.id src dst bytes answers,dataEvents ctx.id dst answers) := by
  have h0 : wrap 64 dst = dst := Nat.mod_eq_of_lt (by omega)
  have h4 : wrap 64 (dst+4) = dst+4 := Nat.mod_eq_of_lt (by omega)
  have h8 : wrap 64 (dst+8) = dst+8 := Nat.mod_eq_of_lt (by omega)
  have h12 : wrap 64 (dst+12) = dst+12 := Nat.mod_eq_of_lt (by omega)
  have hq0 := hq 0
  have hq1 := hq 1
  have hq2 := hq 2
  have hq3 := hq 3
  norm_num at hq0 hq1 hq2 hq3
  norm_num [Ampere.run,Ampere.step,code,Generated.cp_async_copy.program,beforeRead,beforeRet,word,dataEvents,
    Ampere.scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
    Scalar.liftInteger,Scalar.finishInteger,Scalar.liftKind,Scalar.integerOracle,
    Ptx.Event.step,Scalar.u32Bytes,Ampere.liftScalar,
    assign,Ptx.advance,put,lookup,evalAddr,Ptx.eval,Location.resolve,hq0,hq1,hq2,hq3,h0,h4,h8,h12,
    bind,Except.bind,pure,Except.pure]
  norm_num [wrap]

theorem translated_run (ctx : Scalar.Context) (oracle : Ampere.Oracle) (src dst : Nat) (answers : Answers)
    (hx : lookup "X" ctx.params = some src) (hy : lookup "Y" ctx.params = some dst)
    (hs : src < 2^64) (hd : dst+16 ≤ 2^64) (hb : (oracle.bytes 0).length = 16)
    (hq : ∀ i : Fin 4, oracle.scalar (1+i.val) = .integer (answers i)) :
    Ampere.run ctx oracle code 15 {} =
      .ok (finalState ctx.id src dst (oracle.bytes 0) answers,events ctx.id src dst (oracle.bytes 0) answers) := by
  have hret : Ampere.step ctx oracle code (beforeRet ctx.id src dst (oracle.bytes 0) answers) =
      .ok (finalState ctx.id src dst (oracle.bytes 0) answers,[]) := by
    simp [Ampere.step,code,Generated.cp_async_copy.program,beforeRet,finalState,
      Ampere.scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
      Scalar.liftInteger,Scalar.finishInteger,Ptx.Event.step,Ampere.liftScalar,
      localStep,lookup,bind,Except.bind,pure,Except.pure]
  rw [show 15 = 2+13 by decide,Ampere.run_add,parameters_run ctx oracle src dst hx hy hs (by omega)]
  simp only [Except.bind,List.nil_append]
  rw [show 13 = 4+9 by decide,Ampere.run_add,setup_run ctx oracle src dst hs hb]
  simp only [Except.bind]
  rw [show 9 = 8+1 by decide,Ampere.run_add,data_run ctx oracle src dst (oracle.bytes 0) answers hd hq]
  simp [Ampere.run,hret,Except.bind,events]

end
end Ptx.CpAsyncCopyTrace
