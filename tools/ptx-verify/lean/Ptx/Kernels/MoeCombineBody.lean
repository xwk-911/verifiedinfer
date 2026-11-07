import Ptx.Kernels.MoeCombineAddress
import Ptx.Scalar.Replies

/-! Actual single H load, Y store and return, with arbitrary exact-real value.
Address and input-memory agreement remain explicit separate obligations. -/
namespace Ptx.MoeCombine
open Ptx.ISA Ptx.Scalar
noncomputable section

def bodyEvents (i : Inputs) (ctx : Scalar.Context) (expert : Nat) (value : ℝ) : List Scalar.Kind :=
  [.read ⟨.global,hAddress i ctx expert⟩ (Symbolic.encode .f32 value),
   .write ⟨.global,yAddress i ctx⟩ (Symbolic.encode .f32 value)]
def stored (s : Scalar.State) : Scalar.State := {s with core := {s.core with thread := advance s.core.thread}}
def returned (s : Scalar.State) : Scalar.State :=
  finishInteger s {s.core with thread := {s.core.thread with status := .done}}

theorem read_step (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (expert : Nat) (value : ℝ)
    {s : Scalar.State} (hi : Ready i ctx expert s) (ha : AddressBounds i ctx expert)
    (hq : oracle 1 = .real .f32 value) :
    Scalar.step ctx oracle code s = .ok (loadedFloat s "%v" value,
      [.read ⟨.global,hAddress i ctx expert⟩ (Symbolic.encode .f32 value)]) := by
  have h := load_step (ctx := ctx) (oracle := oracle) (code := code) hi.running
    (show code[s.core.thread.pc]? = some (.load .f32 .global "%v" {base := .reg "%hp"}) by rw [hi.pcValue]; rfl)
    (show evalAddr ctx.id.tid.x s.core.thread {base := .reg "%hp"} = .ok (hAddress i ctx expert) by
      simp [evalAddr,Ptx.eval,hi.readPtr,show wrap 64 (hAddress i ctx expert) = hAddress i ctx expert from Nat.mod_eq_of_lt ha.read64])
    (by simpa only [hi.queries] using hq)
  simpa only [loadedFloat,Location.resolve] using h

theorem body_run (i : Inputs) (ctx : Scalar.Context) (oracle : Scalar.Oracle) (expert : Nat) (value : ℝ)
    {s : Scalar.State} (hi : Ready i ctx expert s) (ha : AddressBounds i ctx expert)
    (hq : oracle 1 = .real .f32 value) :
    Scalar.run ctx oracle code 3 s = .ok (returned (stored (loadedFloat s "%v" value)),bodyEvents i ctx expert value) ∧
      (returned (stored (loadedFloat s "%v" value))).core.thread.status = .done ∧
      (returned (stored (loadedFloat s "%v" value))).core.queries = 2 := by
  let next := loadedFloat s "%v" value
  have hread := read_step i ctx oracle expert value hi ha hq
  have hr : next.core.thread.status = .running := hi.running
  have hpc : next.core.thread.pc = 39 := by simp [next,loadedFloat,writeFloat,advance,hi.pcValue]
  have hptr : lookup "%yp" next.core.thread.regs = some (yAddress i ctx) := by simpa [next] using hi.writePtr
  have hstore : Scalar.step ctx oracle code next = .ok (stored next,
      [.write ⟨.global,yAddress i ctx⟩ (Symbolic.encode .f32 value)]) := by
    have hs := store_step (ctx := ctx) (oracle := oracle) (code := code) (s := next)
      (space := .global) (format := .f32) (address := {base := .reg "%yp"}) (value := .reg "%v")
      (addr := yAddress i ctx) (x := value) hr (by rw [hpc]; rfl)
      (by simp [evalAddr,Ptx.eval,hptr,show wrap 64 (yAddress i ctx) = yAddress i ctx from Nat.mod_eq_of_lt ha.write64])
      (by simp [Scalar.eval,next,require,bind,Except.bind,pure,Except.pure])
    simpa only [stored,Location.resolve] using hs
  have hret : Scalar.step ctx oracle code (stored next) = .ok (returned (stored next),[]) := by
    apply integer_local_step (ctx := ctx) (oracle := oracle) (code := code) (s := stored next)
      (instruction := .ret) hr (by simp [stored,advance,hpc,code,Generated.moe_combine.program]) rfl (by intro bid h; cases h)
    rfl
  refine ⟨?_,rfl,?_⟩
  · simp [Scalar.run,hread,hstore,hret,next,bodyEvents,Except.bind]
  · change s.core.queries+1 = 2
    rw [hi.queries]

theorem completed_body {i ctx oracle expert s n last events} (hi : Ready i ctx expert s)
    (ha : AddressBounds i ctx expert) (hn : Scalar.run ctx oracle code n s = .ok (last,events))
    (hd : last.core.thread.status = .done) :
    oracle 1 = .real .f32 (Scalar.replyReal oracle 1) ∧ n = 3 ∧
      events = bodyEvents i ctx expert (Scalar.replyReal oracle 1) := by
  obtain ⟨next,emitted,hs⟩ := step_after_running_prefix hn hd (show Scalar.run ctx oracle code 0 s = .ok (s,[]) from rfl) hi.running
  obtain ⟨value,hq⟩ := real_reply_of_successful_load hi.running
    (show code[s.core.thread.pc]? = some (.load .f32 .global "%v" {base := .reg "%hp"}) by rw [hi.pcValue]; rfl) hs
  have hq1 : oracle 1 = .real .f32 value := by simpa only [hi.queries] using hq
  obtain ⟨hrun,hdone,_⟩ := body_run i ctx oracle expert value hi ha hq1
  have he := complete_run_unique hn hd hrun hdone
  exact ⟨by simpa only [Scalar.replyReal_of_typed hq1] using hq1,he.1,
    by simpa only [Scalar.replyReal_of_typed hq1] using he.2.2⟩

end
end Ptx.MoeCombine
