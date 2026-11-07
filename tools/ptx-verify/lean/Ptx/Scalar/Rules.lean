import Ptx.Scalar.Thread

/-! Reusable register-bank, arithmetic and typed-oracle rules for the scalar
extension. These are local semantic facts, not weak-memory kernel contracts.
-/
namespace Ptx.Scalar
open Ptx.ISA
noncomputable section

theorem lookup_filter_name (name : String) (test : String → Bool) (bindings : List (String × α)) :
    declarationLookup name (bindings.filter (fun kv => test kv.1)) =
      if test name then declarationLookup name bindings else none := by
  induction bindings with
  | nil => simp [declarationLookup]
  | cons head tail ih =>
    rcases head with ⟨key,value⟩
    by_cases hk : key = name
    · subst key
      by_cases ht : test name = true <;> simp [declarationLookup,ht,ih]
    · by_cases ht : test key = true <;> simp [declarationLookup,hk,ht,ih]

theorem integer_lookup_filter_same (name : String) (bindings : Bindings) :
    lookup name (bindings.filter (fun kv => kv.1 != name)) = none := by
  induction bindings with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨key,value⟩
    by_cases hk : key = name
    · subst key; simp [ih]
    · simp [lookup,hk,ih]

theorem float_write_lookup (s : State) (dst : String) (format : Symbolic.Format) (value : ℝ) :
    declarationLookup dst (writeFloat s dst format value).floats = some (format,value) := by
  simp [writeFloat,declarationLookup]

theorem float_write_invalidates_integer (s : State) (dst : String) (format : Symbolic.Format) (value : ℝ) :
    lookup dst (writeFloat s dst format value).core.thread.regs = none := integer_lookup_filter_same dst _

theorem float_write_frame (s : State) (dst other : String) (format : Symbolic.Format) (value : ℝ) (hn : other ≠ dst) :
    declarationLookup other (writeFloat s dst format value).floats = declarationLookup other s.floats ∧
      lookup other (writeFloat s dst format value).core.thread.regs = lookup other s.core.thread.regs := by
  constructor
  · simp only [writeFloat,declarationLookup,show (dst == other) = false from by simp [Ne.symm hn],Bool.false_eq_true,ite_false]
    rw [lookup_filter_name other (fun name => name != dst) s.floats]
    simp [hn]
  · exact lookup_filter_other hn _

def BanksDisjoint (s : State) : Prop :=
  ∀ name, lookup name s.core.thread.regs = none ∨ declarationLookup name s.floats = none

theorem empty_banks_disjoint : BanksDisjoint {} := by intro name; exact Or.inl rfl

theorem write_float_disjoint {s : State} (hi : BanksDisjoint s) (dst : String) (format : Symbolic.Format) (value : ℝ) :
    BanksDisjoint (writeFloat s dst format value) := by
  intro name
  by_cases hn : name = dst
  · subst name; exact Or.inl (float_write_invalidates_integer s dst format value)
  · obtain ⟨hf,hu⟩ := float_write_frame s dst name format value hn
    rw [hf,hu]
    exact hi name

theorem finish_integer_lookup (s : State) (next : Event.State) (name : String) :
    declarationLookup name (finishInteger s next).floats =
      if lookup name next.thread.regs = none then declarationLookup name s.floats else none := by
  change declarationLookup name (s.floats.filter (fun kv => lookup kv.1 next.thread.regs == none)) = _
  rw [lookup_filter_name name (fun key => lookup key next.thread.regs == none) s.floats]
  simp only [beq_iff_eq]

theorem finish_integer_disjoint (s : State) (next : Event.State) : BanksDisjoint (finishInteger s next) := by
  intro name
  by_cases hn : lookup name next.thread.regs = none
  · exact Or.inl hn
  · right
    simp [finish_integer_lookup,hn]

theorem finish_integer_float_frame (s : State) (next : Event.State) (name : String)
    (hn : lookup name next.thread.regs = none) :
    declarationLookup name (finishInteger s next).floats = declarationLookup name s.floats := by
  simp [finish_integer_lookup,hn]

theorem finish_integer_invalidates_float (s : State) (next : Event.State) (name : String)
    (hn : lookup name next.thread.regs ≠ none) : declarationLookup name (finishInteger s next).floats = none := by
  simp [finish_integer_lookup,hn]

theorem eval_written_float (s : State) (dst : String) (format : Symbolic.Format) (value : ℝ) :
    eval format (writeFloat s dst format value) (.reg dst) = .ok value := by
  simp [eval,float_write_lookup,require,bind,Except.bind,pure,Except.pure]

theorem fma_step {ctx oracle code s format dst a b c x y z}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.fmaRn format dst a b c))
    (ha : eval format s a = .ok x) (hb : eval format s b = .ok y) (hz : eval format s c = .ok z) :
    step ctx oracle code s = .ok (writeFloat s dst format (x*y+z),[]) := by
  simp [step,hr,hc,require,ha,hb,hz,bind,Except.bind,pure,Except.pure]

theorem mov_float_step {ctx oracle code s format dst src value}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.mov format dst src))
    (hv : eval format s src = .ok value) :
    step ctx oracle code s = .ok (writeFloat s dst format value,[]) := by
  simp [step,hr,hc,require,hv,bind,Except.bind,pure,Except.pure]

theorem sub_float_step {ctx oracle code s format dst a b x y}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.subRn format dst a b))
    (ha : eval format s a = .ok x) (hb : eval format s b = .ok y) :
    step ctx oracle code s = .ok (writeFloat s dst format (x-y),[]) := by
  simp [step,hr,hc,require,ha,hb,bind,Except.bind,pure,Except.pure]

theorem mul_float_step {ctx oracle code s format dst a b x y}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.mulRn format dst a b))
    (ha : eval format s a = .ok x) (hb : eval format s b = .ok y) :
    step ctx oracle code s = .ok (writeFloat s dst format (x*y),[]) := by
  simp [step,hr,hc,require,ha,hb,bind,Except.bind,pure,Except.pure]

theorem max_float_step {ctx oracle code s format dst a b x y}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.max format dst a b))
    (ha : eval format s a = .ok x) (hb : eval format s b = .ok y) :
    step ctx oracle code s = .ok (writeFloat s dst format (max x y),[]) := by
  simp [step,hr,hc,require,ha,hb,bind,Except.bind,pure,Except.pure]

theorem ex2_float_step {ctx oracle code s dst src value}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.ex2Approx dst src))
    (hv : eval .f32 s src = .ok value) :
    step ctx oracle code s = .ok (writeFloat s dst .f32 (RealMath.exp2 value),[]) := by
  simp [step,hr,hc,require,hv,bind,Except.bind,pure,Except.pure]

theorem div_float_step {ctx oracle code s format dst a b x y}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.divRn format dst a b))
    (ha : eval format s a = .ok x) (hb : eval format s b = .ok y) (hy : y ≠ 0) :
    step ctx oracle code s = .ok (writeFloat s dst format (x/y),[]) := by
  simp [step,hr,hc,require,ha,hb,hy,bind,Except.bind,pure,Except.pure]

theorem div_zero_rejected {ctx oracle code s format dst a b x}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.divRn format dst a b))
    (ha : eval format s a = .ok x) (hb : eval format s b = .ok 0) :
    step ctx oracle code s = .error .zeroDivisor := by
  simp [step,hr,hc,require,ha,hb,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

theorem read_special_step {ctx oracle code s dst source}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.readSpecial dst source)) :
    step ctx oracle code s = .ok
      (finishInteger s {s.core with thread := assign s.core.thread dst (wrap 32 (source.value ctx))},[]) := by
  simp [step,hr,hc,require,bind,Except.bind,pure,Except.pure]

theorem read_special_value {ctx oracle code s dst source next events}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.readSpecial dst source))
    (hs : step ctx oracle code s = .ok (next,events)) :
    lookup dst next.core.thread.regs = some (wrap 32 (source.value ctx)) ∧
      declarationLookup dst next.floats = none ∧ events = [] := by
  rw [read_special_step hr hc] at hs
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj hs)
  refine ⟨lookup_put_same _ _ _,?_,rfl⟩
  apply finish_integer_invalidates_float
  simp [assign,lookup,put]

theorem load_step {ctx oracle code s format space dst address addr value}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.load format space dst address))
    (ha : evalAddr ctx.id.tid.x s.core.thread address = .ok addr)
    (ho : oracle s.core.queries = .real format value) :
    step ctx oracle code s = .ok
      (let next := writeFloat s dst format value
       ({next with core := {next.core with queries := s.core.queries+1}},
        [.read (Location.resolve space ctx.id addr) (Symbolic.encode format value)])) := by
  simp [step,hr,hc,ha,ho,require,liftInteger,bind,Except.bind,pure,Except.pure]

theorem store_step {ctx oracle code s format space address value addr x}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.store format space address value))
    (ha : evalAddr ctx.id.tid.x s.core.thread address = .ok addr) (hv : eval format s value = .ok x) :
    step ctx oracle code s = .ok
      ({s with core := {s.core with thread := advance s.core.thread}},
        [.write (Location.resolve space ctx.id addr) (Symbolic.encode format x)]) := by
  simp [step,hr,hc,ha,hv,require,liftInteger,bind,Except.bind,pure,Except.pure]

theorem integer_load_real_oracle_rejected {ctx oracle code s space dst address format value}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.integer (.load space dst address)))
    (ho : oracle s.core.queries = .real format value) : step ctx oracle code s = .error (.oracleType s.core.queries) := by
  simp [step,hr,hc,ho,require,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

theorem real_load_integer_oracle_rejected {ctx oracle code s format space dst address addr value}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.load format space dst address))
    (ha : evalAddr ctx.id.tid.x s.core.thread address = .ok addr)
    (ho : oracle s.core.queries = .integer value) : step ctx oracle code s = .error (.oracleType s.core.queries) := by
  simp [step,hr,hc,ha,ho,require,liftInteger,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

theorem integer_reply_of_successful_load {ctx oracle code s next events space dst address}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.integer (.load space dst address)))
    (hs : step ctx oracle code s = .ok (next,events)) :
    ∃ value, oracle s.core.queries = .integer value := by
  cases ho : oracle s.core.queries with
  | integer value => exact ⟨value,rfl⟩
  | real format value => rw [integer_load_real_oracle_rejected hr hc ho] at hs; cases hs

theorem real_reply_of_successful_load {ctx oracle code s next events format space dst address}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.load format space dst address))
    (hs : step ctx oracle code s = .ok (next,events)) :
    ∃ value, oracle s.core.queries = .real format value := by
  cases ha : evalAddr ctx.id.tid.x s.core.thread address with
  | error fault =>
    simp [step,hr,hc,ha,require,liftInteger,bind,Except.bind] at hs
  | ok addr =>
    cases ho : oracle s.core.queries with
    | integer value =>
      simp [step,hr,hc,ha,ho,require,liftInteger,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
    | real actual value =>
      by_cases hf : actual = format
      · subst actual
        exact ⟨value,rfl⟩
      · simp [step,hr,hc,ha,ho,hf,require,liftInteger,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs

theorem step_banks_disjoint {ctx oracle code s next events}
    (hi : BanksDisjoint s) (hs : step ctx oracle code s = .ok (next,events)) : BanksDisjoint next := by
  by_cases hr : s.core.thread.status = .running
  · cases hc : code[s.core.thread.pc]? with
    | none => simp [step,hr,hc,require,bind,Except.bind] at hs
    | some instruction =>
      cases instruction <;> simp [step,hr,hc,require,bind,Except.bind,pure,Except.pure,
        throw,throwThe,MonadExceptOf.throw] at hs
      all_goals try (obtain ⟨rfl,rfl⟩ := hs; exact finish_integer_disjoint _ _)
      all_goals
        repeat' first | split at hs | (cases hs)
        all_goals first
          | exact hi
          | exact write_float_disjoint hi _ _ _
          | exact finish_integer_disjoint _ _
  · simp [step,hr,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs

theorem runs_banks_disjoint {ctx oracle code s next events}
    (hs : Runs ctx oracle code s events next) (hi : BanksDisjoint s) : BanksDisjoint next := by
  induction hs with
  | nil => exact hi
  | cons hstep _ ih => exact ih (step_banks_disjoint hi hstep)

theorem run_banks_disjoint {ctx oracle code n s next events}
    (hs : run ctx oracle code n s = .ok (next,events)) (hi : BanksDisjoint s) : BanksDisjoint next :=
  runs_banks_disjoint (run_sound hs) hi

end
end Ptx.Scalar
