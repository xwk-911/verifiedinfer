import Ptx.Kernels.FloatLiteralsMemory

/-! Reconstruct every complete, provenance-checked trace of the actual generated
float-literal program. Unused oracle replies, instruction counts and trace-list
order are unrestricted. Correctness then transfers to the shared memory model.
-/
namespace Ptx.FloatLiteralsUniversal
open Ptx.ISA Ptx.Event Ptx.Scalar
open Ptx.FloatLiteralsMemory
noncomputable section

def beforeRead (dst : Nat) : Scalar.State := {
  core := {thread := {pc := 5,regs := [("%ptr",dst)]}}
  floats := [("%f2",(.f32,9)),("%f1",(.f32,3)),("%f0",(.f32,1))]
}

theorem prefix_run (ctx : Scalar.Context) (oracle : Scalar.Oracle) (dst : Nat)
    (hp : lookup "dst" ctx.params = some dst) (hd : dst < 2^64) :
    Scalar.run ctx oracle FloatLiteralsTrace.code 5 {} =
      .ok (beforeRead dst,[.write ⟨.shared ctx.id.cta,0⟩ (Symbolic.encode .f32 9)]) := by
  rw [show 5 = 1+4 by decide,Scalar.run_add,FloatLiteralsTrace.parameters_run ctx oracle dst hp hd]
  simp only [Except.bind,List.nil_append]
  norm_num [Scalar.run,Scalar.step,FloatLiteralsTrace.code,Generated.float_literals.program,
    FloatLiteralsTrace.ready,beforeRead,Scalar.eval,F32Literal.value,writeFloat,Scalar.require,
    liftInteger,evalAddr,Ptx.eval,advance,lookup,declarationLookup,Location.resolve,wrap,
    bind,Except.bind,pure,Except.pure]

theorem complete_oracle_reply {ctx oracle dst n last events}
    (hp : lookup "dst" ctx.params = some dst) (hd : dst < 2^64)
    (hn : Scalar.run ctx oracle FloatLiteralsTrace.code n {} = .ok (last,events))
    (hc : last.core.thread.status = .done) : ∃ answer, oracle 0 = .real .f32 answer := by
  have hcount := completed_after_running_prefix hn hc (prefix_run ctx oracle dst hp hd) rfl
  obtain ⟨mid,headEvents,h6⟩ := successful_prefix (by omega : 6 ≤ n) hn
  rw [show 6 = 5+1 by decide,Scalar.run_add,prefix_run ctx oracle dst hp hd] at h6
  simp only [Except.bind] at h6
  cases hq : oracle 0 with
  | integer value =>
    simp [Scalar.run,Scalar.step,FloatLiteralsTrace.code,Generated.float_literals.program,
      beforeRead,Scalar.require,liftInteger,evalAddr,Ptx.eval,hq,
      bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at h6
  | real format answer =>
    cases format with
    | f32 => exact ⟨answer,rfl⟩
    | f16 =>
      simp [Scalar.run,Scalar.step,FloatLiteralsTrace.code,Generated.float_literals.program,
        beforeRead,Scalar.require,liftInteger,evalAddr,Ptx.eval,hq,
        bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at h6
    | f64 =>
      simp [Scalar.run,Scalar.step,FloatLiteralsTrace.code,Generated.float_literals.program,
        beforeRead,Scalar.require,liftInteger,evalAddr,Ptx.eval,hq,
        bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at h6

theorem run_with_oracle (ctx : Scalar.Context) (oracle : Scalar.Oracle) (dst : Nat) (answer : ℝ)
    (hq : oracle 0 = .real .f32 answer) (hp : lookup "dst" ctx.params = some dst) (hd : dst < 2^64) :
    Scalar.run ctx oracle FloatLiteralsTrace.code 8 {} =
      .ok (FloatLiteralsTrace.finalState dst answer,FloatLiteralsTrace.events ctx.id dst answer) := by
  have hdst : wrap 64 dst = dst := Nat.mod_eq_of_lt hd
  simp only [wrap] at hdst
  rw [show 8 = 5+3 by decide,Scalar.run_add,prefix_run ctx oracle dst hp hd]
  simp only [Except.bind]
  -- The final integer return is checked by the existing local rule, avoiding
  -- any replacement of mixed float instructions with an integer certificate.
  have hret : Scalar.step ctx oracle FloatLiteralsTrace.code (FloatLiteralsTrace.beforeRet dst answer) =
      .ok (FloatLiteralsTrace.finalState dst answer,[]) := by
    have h := Scalar.integer_local_step (ctx := ctx) (oracle := oracle)
      (code := FloatLiteralsTrace.code) (s := FloatLiteralsTrace.beforeRet dst answer)
      rfl rfl rfl (by intro bid h; cases h) rfl
    simpa [finishInteger,FloatLiteralsTrace.beforeRet,FloatLiteralsTrace.finalState,lookup] using h
  have hbody : Scalar.run ctx oracle FloatLiteralsTrace.code 2 (beforeRead dst) =
      .ok (FloatLiteralsTrace.beforeRet dst answer,
        [.read ⟨.shared ctx.id.cta,0⟩ (Symbolic.encode .f32 answer),
         .write ⟨.global,dst⟩ (Symbolic.encode .f32 answer)]) := by
    simp [Scalar.run,Scalar.step,FloatLiteralsTrace.code,Generated.float_literals.program,
      beforeRead,FloatLiteralsTrace.beforeRet,Scalar.eval,writeFloat,Scalar.require,
      liftInteger,evalAddr,Ptx.eval,advance,lookup,declarationLookup,Location.resolve,hq,hdst,wrap,
      bind,Except.bind,pure,Except.pure]
  rw [show 3 = 2+1 by decide,Scalar.run_add,hbody]
  simp [Scalar.run,hret,Except.bind,FloatLiteralsTrace.events]

theorem trace_shape {dst params t block}
    (hp : lookup "dst" params = some dst) (hd : dst < 2^64)
    (hr : Scalar.Produced FloatLiteralsTrace.code params t block) (hc : t.final.thread.status = .done) :
    ∃ answer, t.count = 8 ∧ t.final = (FloatLiteralsTrace.finalState dst answer).core ∧
      t.events = FloatLiteralsTrace.events t.id dst answer := by
  obtain ⟨floats,hr⟩ := hr
  obtain ⟨answer,hq⟩ := complete_oracle_reply hp hd hr hc
  have hs := Scalar.complete_run_unique hr hc (run_with_oracle {id := t.id,params := params,block := block} t.oracle dst answer hq hp hd) rfl
  exact ⟨answer,hs.1,congrArg Scalar.State.core hs.2.1,hs.2.2⟩

def Pre (dst : Nat) (l : Scalar.Launch) : Prop :=
  dst < 2^64 ∧ l.geometry = ⟨.one,.one⟩ ∧ lookup "dst" l.params = some dst

theorem candidate_view {dst l c}
    (hp : Pre dst l) (hw : Scalar.WellFormed FloatLiteralsTrace.code l c) (hc : c.Complete) :
    ∃ answer, SameEvents c (graph dst answer) := by
  obtain ⟨t,ht,htid⟩ := hw.2.2.2 thread
    (by rw [hp.2.1]; simp [thread,ThreadId.Valid,Dim3.Within,Dim3.one,Dim3.zero])
  obtain ⟨answer,_,_,hshape⟩ := trace_shape hp.2.2 hp.1 (hw.2.2.1 t ht).2 (hc t ht)
  rw [htid] at hshape
  refine ⟨answer,?_⟩
  funext id
  rw [FloatLiteralsMemory.eventAt]
  by_cases hi : id.thread = thread
  · rw [eventAt_of_trace hw.2.1 ht (hi.trans htid.symm),hshape]
    simp only [hi,↓reduceIte]
  · have hn : c.eventAt id = none := by
      cases he : c.eventAt id with
      | none => rfl
      | some kind =>
        obtain ⟨u,hu,hui,_⟩ := eventAt_trace he
        have hv := (hw.2.2.1 u hu).1
        rw [hp.2.1] at hv
        exact (hi (hui.symm.trans (valid_thread_unique hv))).elim
    simp only [hi,↓reduceIte,hn]

theorem barriers (dst : Nat) (answer : ℝ) : BarrierParticipation (graph dst answer) := by
  intro leave bid generation he
  exact (no_returns dst answer leave bid generation he).elim

theorem control_acyclic (dst : Nat) (answer : ℝ) : BarrierControlAcyclic (graph dst answer) := by
  intro id hp
  have hlt := hp.rank_lt (fun id => id.serial) (by
    intro a b he
    rcases he with hpo | hsync | hexit
    · exact hpo.2.2.2
    · obtain ⟨_,bid,generation,_,hb⟩ := hsync
      exact (no_returns dst answer b bid generation hb).elim
    · obtain ⟨_,t,_,_,_,bid,generation,hb,_⟩ := hexit
      exact (no_returns dst answer b bid generation hb).elim)
  exact Nat.lt_irrefl _ hlt

theorem correct (dst : Nat) :
    Scalar.Triple FloatLiteralsTrace.code (Pre dst) (fun _ => domain dst)
      (fun _ output => observedValue dst output = some 9) := by
  intro l c rf co o hp hw hm ho hd
  obtain ⟨answer,he⟩ := candidate_view hp hw ho.complete
  have hg := he.memory (barriers dst answer) (control_acyclic dst answer) hm
  have hob := he.observation (complete dst answer) ho
  exact output_correct hg hob hd

theorem witness_wellFormed {dst l} (hp : Pre dst l) :
    Scalar.WellFormed FloatLiteralsTrace.code l (graph dst 9) := by
  refine ⟨by rw [hp.2.1]; simp [Geometry.Valid,Dim3.Positive,Dim3.one],by simp [graph],?_,?_⟩
  · intro t ht
    simp only [graph,List.mem_singleton] at ht
    subst t
    refine ⟨?_,?_⟩
    · simp [trace,thread,ThreadId.Valid,Dim3.Within,hp.2.1,Dim3.one,Dim3.zero]
    · exact ⟨(FloatLiteralsTrace.finalState dst 9).floats,
        FloatLiteralsTrace.translated_trace {id := thread,params := l.params,block := l.geometry.block} dst 9 hp.2.2 hp.1⟩
  · intro id hv
    rw [hp.2.1] at hv
    exact ⟨trace dst 9,by simp [graph],(valid_thread_unique hv).symm⟩

theorem nonvacuous (dst : Nat) :
    Scalar.Nonvacuous FloatLiteralsTrace.code (Pre dst) (fun _ => domain dst) := by
  intro l hp
  exact ⟨graph dst 9,fun _ _ => .write storeId,InitialCo (graph dst 9),observation dst l.initial,
    witness_wellFormed hp,consistent dst l.initial,observed dst l.initial,rfl⟩

end
end Ptx.FloatLiteralsUniversal
