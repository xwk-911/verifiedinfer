import Ptx.Kernels.CpAsyncCopyTrace
import Mathlib.Tactic.FinCases

/-! Invert arbitrary successful complete runs of the actual helper. Finite
instruction count and integer reply shapes are derived from source execution;
copy contents and integer values are still independent and unconstrained. -/
namespace Ptx.CpAsyncCopyTrace
open Ptx.ISA Ptx.Ampere
noncomputable section

def betweenPairs (id : ThreadId) (src dst : Nat) (bytes : List Symbolic.Byte) (done previous : Nat) : State := {
  scalar := {core := {thread := {pc := 6+2*done,regs := (if done = 0 then [] else [("%v",previous)]) ++ [("%y",dst),("%x",src)]},queries := 1+done,generations := [(0,1)]}}
  copies := [operation id src bytes]
  groups := 1
}

theorem pair_run (ctx : Scalar.Context) (oracle : Ampere.Oracle) (src dst : Nat)
    (bytes : List Symbolic.Byte) (i : Fin 4) (previous answer : Nat)
    (hd : dst+16 ≤ 2^64) (hq : oracle.scalar (1+i.val) = .integer answer) :
    Ampere.run ctx oracle code 2 (betweenPairs ctx.id src dst bytes i.val previous) =
      .ok (betweenPairs ctx.id src dst bytes (i.val+1) (wrap 32 answer),
        [.ordinary (.read ⟨.shared ctx.id.cta,4*i.val⟩ (Scalar.u32Bytes (wrap 32 answer))),
         .ordinary (.write ⟨.global,dst+4*i.val⟩ (Scalar.u32Bytes (wrap 32 answer)))]) := by
  have haddress : wrap 64 (dst+4*i.val) = dst+4*i.val := Nat.mod_eq_of_lt (by have := i.isLt; omega)
  fin_cases i
  all_goals
    norm_num at hq haddress
    norm_num [Ampere.run,Ampere.step,code,Generated.cp_async_copy.program,betweenPairs,
      Ampere.scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
      Scalar.liftInteger,Scalar.finishInteger,Scalar.liftKind,Scalar.integerOracle,
      Ptx.Event.step,Scalar.u32Bytes,Ampere.liftScalar,
      assign,Ptx.advance,put,lookup,evalAddr,Ptx.eval,Location.resolve,hq,haddress,
      bind,Except.bind,pure,Except.pure]
    norm_num [wrap]

theorem completed_copy_size {ctx oracle src dst n last emitted}
    (hx : lookup "X" ctx.params = some src) (hy : lookup "Y" ctx.params = some dst)
    (hs : src < 2^64) (hd : dst+16 ≤ 2^64)
    (hn : Ampere.run ctx oracle code n {} = .ok (last,emitted))
    (hc : last.scalar.core.thread.status = .done) : (oracle.bytes 0).length = 16 := by
  obtain ⟨next,events,hstep⟩ := Ampere.step_after_running_prefix hn hc
    (parameters_run ctx oracle src dst hx hy hs (by omega)) rfl
  by_contra hb
  have hsrc : wrap 64 src = src := Nat.mod_eq_of_lt hs
  norm_num [Ampere.step,ready,code,Generated.cp_async_copy.program,CopySize,
    Ampere.liftInteger,evalAddr,Ptx.eval,lookup,hsrc,hb,wrap,
    bind,Except.bind,pure,Except.pure] at hstep

theorem completed_pair_reply {ctx oracle src dst bytes n last emitted i previous k headEvents}
    (hn : Ampere.run ctx oracle code n {} = .ok (last,emitted))
    (hc : last.scalar.core.thread.status = .done)
    (hp : Ampere.run ctx oracle code k {} = .ok (betweenPairs ctx.id src dst bytes i.val previous,headEvents)) :
    ∃ answer, oracle.scalar (1+(i : Fin 4).val) = .integer answer := by
  obtain ⟨next,events,hstep⟩ := Ampere.step_after_running_prefix hn hc hp rfl
  cases hq : oracle.scalar (1+i.val) with
  | integer answer => exact ⟨answer,rfl⟩
  | real format value =>
    fin_cases i
    all_goals
      norm_num at hq
      norm_num [Ampere.step,code,Generated.cp_async_copy.program,betweenPairs,
        Ampere.scalarSkeleton,Scalar.step,Scalar.require,Scalar.integer_delegate_fetch,
        Ampere.liftScalar,hq,bind,Except.bind,pure,Except.pure] at hstep

theorem completed_pair_advance {ctx oracle src dst bytes n last emitted i previous k headEvents}
    (hd : dst+16 ≤ 2^64)
    (hn : Ampere.run ctx oracle code n {} = .ok (last,emitted))
    (hc : last.scalar.core.thread.status = .done)
    (hp : Ampere.run ctx oracle code k {} = .ok (betweenPairs ctx.id src dst bytes (i : Fin 4).val previous,headEvents)) :
    ∃ answer more, oracle.scalar (1+i.val) = .integer answer ∧
      Ampere.run ctx oracle code (k+2) {} =
        .ok (betweenPairs ctx.id src dst bytes (i.val+1) (wrap 32 answer),headEvents++more) := by
  obtain ⟨answer,hq⟩ := completed_pair_reply hn hc hp
  refine ⟨answer,[.ordinary (.read ⟨.shared ctx.id.cta,4*i.val⟩ (Scalar.u32Bytes (wrap 32 answer))),
    .ordinary (.write ⟨.global,dst+4*i.val⟩ (Scalar.u32Bytes (wrap 32 answer)))],hq,?_⟩
  rw [Ampere.run_add,hp]
  simp only [Except.bind]
  rw [pair_run ctx oracle src dst bytes i previous answer hd hq]

theorem completed_replies {ctx oracle src dst n last emitted}
    (hx : lookup "X" ctx.params = some src) (hy : lookup "Y" ctx.params = some dst)
    (hs : src < 2^64) (hd : dst+16 ≤ 2^64)
    (hn : Ampere.run ctx oracle code n {} = .ok (last,emitted))
    (hc : last.scalar.core.thread.status = .done) :
    (oracle.bytes 0).length = 16 ∧ ∃ answers : Answers, ∀ i : Fin 4, oracle.scalar (1+i.val) = .integer (answers i) := by
  have hb := completed_copy_size hx hy hs hd hn hc
  refine ⟨hb,?_⟩
  have hprefix : Ampere.run ctx oracle code 6 {} =
      .ok (betweenPairs ctx.id src dst (oracle.bytes 0) 0 0,
        [.issue 0 (operation ctx.id src (oracle.bytes 0)),.commit 0,.wait 1 0,
         .ordinary (.barrierArrival 0 0),.ordinary (.barrierReturn 0 0)]) := by
    rw [show 6 = 2+4 by decide,Ampere.run_add,parameters_run ctx oracle src dst hx hy hs (by omega)]
    simp only [Except.bind]
    rw [setup_run ctx oracle src dst hs hb]
    rfl
  obtain ⟨a,ea,ha,h8⟩ := completed_pair_advance (i := (0 : Fin 4)) hd hn hc hprefix
  obtain ⟨b,eb,hb',h10⟩ := completed_pair_advance (i := (1 : Fin 4)) hd hn hc h8
  obtain ⟨c,ec,hc',h12⟩ := completed_pair_advance (i := (2 : Fin 4)) hd hn hc h10
  obtain ⟨d,_,hd',_⟩ := completed_pair_advance (i := (3 : Fin 4)) hd hn hc h12
  refine ⟨fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d,?_⟩
  intro i
  fin_cases i
  · exact ha
  · exact hb'
  · exact hc'
  · exact hd'

theorem complete_source_shape {ctx oracle src dst n last emitted}
    (hx : lookup "X" ctx.params = some src) (hy : lookup "Y" ctx.params = some dst)
    (hs : src < 2^64) (hd : dst+16 ≤ 2^64)
    (hn : Ampere.run ctx oracle code n {} = .ok (last,emitted))
    (hc : last.scalar.core.thread.status = .done) :
    ∃ answers : Answers, (oracle.bytes 0).length = 16 ∧
      (∀ i : Fin 4, oracle.scalar (1+i.val) = .integer (answers i)) ∧ n = 15 ∧
      last = finalState ctx.id src dst (oracle.bytes 0) answers ∧
      emitted = events ctx.id src dst (oracle.bytes 0) answers := by
  obtain ⟨hb,answers,hq⟩ := completed_replies hx hy hs hd hn hc
  have hcand := translated_run ctx oracle src dst answers hx hy hs hd hb hq
  have hshape := Ampere.complete_run_unique hn hc hcand rfl
  exact ⟨answers,hb,hq,hshape⟩

end
end Ptx.CpAsyncCopyTrace
