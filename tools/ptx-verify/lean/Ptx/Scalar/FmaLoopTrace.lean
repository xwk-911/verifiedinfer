import Ptx.Scalar.FmaLoop

/-! Extract typed load replies from arbitrary successful completed executions.
No correct-input oracle or execution bound is assumed. Initial loop invariants
and layout bounds remain explicit; global memory contracts are separate.
-/
namespace Ptx.Scalar.FmaLoop
open Ptx.ISA Ptx.Scalar Ptx.ScalarMatmul
noncomputable section

def guarded (base : Nat) (s : Scalar.State) : Scalar.State := intPC (intAssign s "%p" 0) (base+2)

theorem guard_run {code : List Scalar.Instr} {base origin : Nat} (fragment : Fragment code base) (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {k : Nat} {acc : ℝ} {s : Scalar.State} (hi : Inv base origin l k acc s) (hk : k < l.count) :
    Scalar.run ctx oracle code 2 s = .ok (guarded base s,[]) := by
  have hk32 : wrap 32 k = k := Nat.mod_eq_of_lt (by have := l.count32; omega)
  have hK32 : wrap 32 l.count = l.count := Nat.mod_eq_of_lt l.count32
  have h32 : Scalar.step ctx oracle code s = .ok (intAssign s "%p" 0,[]) := by
    apply Scalar.integer_local_step hi.running (by rw [hi.pc]; exact fragment.guard) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,hi.index,hi.bound,hk32,hK32,Nat.not_le_of_lt hk,
      bind,Except.bind,pure,Except.pure]
  have h33 : Scalar.step ctx oracle code (intAssign s "%p" 0) = .ok (guarded base s,[]) := by
    apply Scalar.integer_local_step (instruction := .branch "%p" true (base+9))
      (by simpa [intAssign,finishInteger,assign,advance] using hi.running)
      (by simpa [intAssign,finishInteger,assign,advance,hi.pc] using fragment.branch)
      rfl (by intro bid h; cases h)
    simp [localStep,intAssign,finishInteger,assign,advance,hi.pc,bind,Except.bind,pure,Except.pure]
  simp [Scalar.run,h32,h33,Except.bind]

theorem completed_iteration_replies {code : List Scalar.Instr} {base origin : Nat} (fragment : Fragment code base) (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {k n : Nat} {acc : ℝ} {s final : Scalar.State} {events : List Scalar.Kind}
    (hi : Inv base origin l k acc s) (hk : k < l.count)
    (hr : Scalar.run ctx oracle code n s = .ok (final,events)) (hd : final.core.thread.status = .done) :
    ∃ a b, oracle (origin+2*k) = .real .f32 a ∧ oracle (origin+2*k+1) = .real .f32 b := by
  have hguard := guard_run fragment l ctx oracle hi hk
  have hgr : (guarded base s).core.thread.status = .running := by
    simpa [guarded,intPC,intAssign,finishInteger,assign,advance] using hi.running
  obtain ⟨mid,emitted,hstep⟩ := step_after_running_prefix hr hd hguard hgr
  obtain ⟨a,hquery⟩ := real_reply_of_successful_load hgr (show code[(guarded base s).core.thread.pc]? =
    some (.load .f32 .global "%av" {base := .reg "%ap"}) by simpa [guarded,intPC,finishInteger] using fragment.loadA) hstep
  have hqa : oracle (origin+2*k) = .real .f32 a := by
    simpa [guarded,intPC,intAssign,finishInteger,hi.queries] using hquery
  let loaded := loadedFloat (guarded base s) "%av" a
  have hload : Scalar.step ctx oracle code (guarded base s) =
      .ok (loaded,[.read ⟨.global,l.aBase+4*k⟩ (Symbolic.encode .f32 a)]) := by
    apply Scalar.load_step (space := .global) (format := .f32) (dst := "%av")
      (address := {base := .reg "%ap"}) (addr := l.aBase+4*k) (value := a)
    · exact hgr
    · simpa [guarded,intPC,finishInteger] using fragment.loadA
    · have h64 : wrap 64 (l.aBase+4*k) = l.aBase+4*k := Nat.mod_eq_of_lt (l.aRead64 k hk)
      simp [evalAddr,Ptx.eval,guarded,hi.aPointer,h64,bind,Except.bind,pure,Except.pure]
    · exact hquery
  have h3 : Scalar.run ctx oracle code 3 s =
      .ok (loaded,[.read ⟨.global,l.aBase+4*k⟩ (Symbolic.encode .f32 a)]) := by
    rw [show 3 = 2+1 by decide,Scalar.run_add,hguard]
    simp [Scalar.run,hload,Except.bind]
  have hlr : loaded.core.thread.status = .running := by
    simpa [loaded,loadedFloat,writeFloat,advance] using hgr
  obtain ⟨next,more,hsecond⟩ := step_after_running_prefix hr hd h3 hlr
  obtain ⟨b,hqb⟩ := real_reply_of_successful_load hlr (show code[loaded.core.thread.pc]? =
    some (.load .f32 .global "%bv" {base := .reg "%bp"}) by simpa [loaded,loadedFloat,writeFloat,guarded,intPC,finishInteger,advance] using fragment.loadB) hsecond
  refine ⟨a,b,hqa,?_⟩
  simpa [loaded,loadedFloat,writeFloat,guarded,intPC,intAssign,finishInteger,hi.queries] using hqb

def realReply (oracle : Scalar.Oracle) (query : Nat) : ℝ :=
  match oracle query with | .real _ value => value | .integer _ => 0

theorem realReply_of_typed {oracle query value} (h : oracle query = .real .f32 value) :
    realReply oracle query = value := by rw [realReply,h]

/-- Every remaining query of a completed run is a typed f32 reply. The fallback
in realReply cannot justify an integer or wrongly formatted reply. -/
theorem completed_replies {code : List Scalar.Instr} {base origin : Nat} (fragment : Fragment code base) (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (remaining : Nat) : ∀ {start n acc s final events}, l.count = start+remaining → Inv base origin l start acc s →
      Scalar.run ctx oracle code n s = .ok (final,events) → final.core.thread.status = .done →
      ∀ k, start ≤ k → k < l.count →
        oracle (origin+2*k) = .real .f32 (realReply oracle (origin+2*k)) ∧
        oracle (origin+2*k+1) = .real .f32 (realReply oracle (origin+2*k+1)) := by
  induction remaining with
  | zero => intro start n acc s final events he hi hr hd k hstart hk; omega
  | succ count ih =>
    intro start n acc s final events he hi hr hd k hstart hk
    have hactive : start < l.count := by omega
    obtain ⟨a,b,ha,hb⟩ := completed_iteration_replies fragment l ctx oracle hi hactive hr hd
    by_cases heq : k = start
    · subst k
      exact ⟨by simpa only [realReply_of_typed ha] using ha,by simpa only [realReply_of_typed hb] using hb⟩
    · obtain ⟨mid,hm,hmid⟩ := iteration fragment l ctx oracle hi hactive ha hb
      have hcount := completed_after_running_prefix hr hd hm hmid.running
      obtain ⟨rest,hn⟩ := Nat.exists_eq_add_of_le (by omega : 9 ≤ n)
      have htail := hr
      rw [hn,Scalar.run_add,hm] at htail
      simp only [Except.bind] at htail
      cases ht : Scalar.run ctx oracle code rest mid with
      | error fault => simp [ht] at htail
      | ok result =>
        rcases result with ⟨last,tailEvents⟩
        simp only [ht,Except.ok.injEq,Prod.mk.injEq] at htail
        have hdone : last.core.thread.status = .done := htail.1 ▸ hd
        exact ih (by omega : l.count = (start+1)+count) hmid ht hdone k (by omega) hk

def replyA (origin : Nat) (oracle : Scalar.Oracle) : Matrix := fun _ k => realReply oracle (origin+2*k)
def replyB (origin : Nat) (oracle : Scalar.Oracle) : Matrix := fun k _ => realReply oracle (origin+2*k+1)

theorem completed_shape {code : List Scalar.Instr} {base origin : Nat} (fragment : Fragment code base) (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {n : Nat} {s final : Scalar.State} {events : List Scalar.Kind} (hi : Inv base origin l 0 0 s)
    (hr : Scalar.run ctx oracle code n s = .ok (final,events)) (hd : final.core.thread.status = .done) :
    n = 9*l.count+4 ∧
      events = loopReads l (replyA origin oracle) (replyB origin oracle) 0 0 0 l.count ++
        [.write ⟨.global,l.output⟩ (Symbolic.encode .f32 (prefixProduct (replyA origin oracle) (replyB origin oracle) 0 0 l.count))] ∧
      Finished base origin l (prefixProduct (replyA origin oracle) (replyB origin oracle) 0 0 l.count) final := by
  have hqueries := completed_replies fragment l ctx oracle l.count (by omega : l.count = 0+l.count) hi hr hd
  obtain ⟨last,hfull,hfinish⟩ := complete_from_entry fragment l ctx oracle (replyA origin oracle) (replyB origin oracle) 0 0
    (fun k hk => (hqueries k (by omega) hk).1) (fun k hk => (hqueries k (by omega) hk).2) hi
  have he := Scalar.complete_run_unique hr hd hfull hfinish.done
  exact ⟨he.1,he.2.2,he.2.1 ▸ hfinish⟩

theorem completed_wrong_type_rejected {code : List Scalar.Instr} {base origin : Nat} (fragment : Fragment code base) (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {s final : Scalar.State} {n value : Nat} {events : List Scalar.Kind}
    (hi : Inv base origin l 0 0 s) (hp : 0 < l.count) (hq : oracle origin = .integer value)
    (hr : Scalar.run ctx oracle code n s = .ok (final,events)) : final.core.thread.status ≠ .done := by
  intro hd
  obtain ⟨a,_,ha,_⟩ := completed_iteration_replies fragment l ctx oracle hi hp hr hd
  simp only [Nat.mul_zero,Nat.add_zero,hq] at ha
  cases ha

end
end Ptx.Scalar.FmaLoop
