import Ptx.Scalar.Syntax
import Ptx.Scalar.RealMath
import Ptx.Event.Thread
import Ptx.Event.Origins
import Ptx.Rules.Local

/-! Fixed mixed integer/real scalar trace semantics. Integer operations delegate
to the existing interpreter at the SAME PC. Float writes invalidate same-name
integer values; integer completion invalidates shadowed float values. This avoids
stale-value "bitcasts" across the two representations. Float arithmetic is exact
real arithmetic. `Scalar.Execution` connects these traces to the shared generic
memory predicates; local traces alone are not kernel verification.
-/
namespace Ptx.Scalar
open Ptx.ISA
noncomputable section

inductive Fault
  | integer (fault : Ptx.Fault)
  | floatRegister (name : String)
  | floatFormat (name : String)
  | oracleType (query : Nat)
  | literalFormat
  /-- Outside the finite-real fragment. This is not PTX's IEEE division-by-zero result. -/
  | zeroDivisor
  deriving Repr, DecidableEq

abbrev FloatBindings := List (String × (Symbolic.Format × ℝ))
structure State where
  core : Event.State := {}
  floats : FloatBindings := []

inductive Reply
  | integer (value : Nat)
  | real (format : Symbolic.Format) (value : ℝ)
abbrev Oracle := Nat → Reply
abbrev Kind := Event.Kind Symbolic.Byte

def require (value : Option α) (fault : Fault) : Except Fault α :=
  match value with | some x => .ok x | none => .error fault
def liftInteger (value : Except Ptx.Fault α) : Except Fault α :=
  match value with | .ok x => .ok x | .error fault => .error (.integer fault)

def eval (format : Symbolic.Format) (s : State) : FloatOperand → Except Fault ℝ
  | .literal value => if format = .f32 then .ok value.value else .error .literalFormat
  | .reg name => do
      let (actual,value) ← require (declarationLookup name s.floats) (.floatRegister name)
      if actual = format then return value else throw (.floatFormat name)

def writeFloat (s : State) (dst : String) (format : Symbolic.Format) (value : ℝ) : State := {
  s with
  core := {s.core with thread := {advance s.core.thread with regs := s.core.thread.regs.filter (fun kv => kv.1 != dst)}}
  floats := (dst,(format,value)) :: s.floats.filter (fun kv => kv.1 != dst)
}

def finishInteger (s : State) (next : Event.State) : State := {
  core := next
  floats := s.floats.filter (fun kv => lookup kv.1 next.thread.regs == none)
}

def liftKind : Event.Kind → Kind
  | .read loc bytes => .read loc (bytes.map Symbolic.Byte.bits)
  | .write loc bytes => .write loc (bytes.map Symbolic.Byte.bits)
  | .rmw scope loc bytes => .rmw scope loc
      ⟨bytes.before.map Symbolic.Byte.bits,bytes.after.map Symbolic.Byte.bits,by simpa using bytes.sameSize⟩
  | .barrierArrival bid generation => .barrierArrival bid generation
  | .barrierReturn bid generation => .barrierReturn bid generation

/-- Private stepping aid. A float slot is intercepted by `step` before delegation;
this skeleton is NEVER a translation or correctness certificate for a float kernel. -/
private def integerSkeleton (code : List Instr) : List Ptx.Instr := code.map (fun i => match i with
  | .integer old => old
  | _ => .ret)

/-- One-step delegate fetch, not an integer interpretation of a mixed program. -/
theorem integer_delegate_fetch (code : List Instr) (pc : Nat) :
    (integerSkeleton code)[pc]? = (code[pc]?).map (fun i => match i with
      | .integer old => old | _ => .ret) := by
  simp only [integerSkeleton,List.getElem?_map]

def integerOracle (oracle : Oracle) (query : Nat) : Nat :=
  match oracle query with | .integer n => n | .real _ _ => 0

def atomicAddBytes (old increment : Nat) : Event.RmwBytes Symbolic.Byte :=
  ⟨(encodeU32 (wrap 32 old)).map Symbolic.Byte.bits,
    (encodeU32 (wrap 32 (wrap 32 old+increment))).map Symbolic.Byte.bits,by simp⟩

def step (ctx : Context) (oracle : Oracle) (code : List Instr) (s : State) : Except Fault (State × List Kind) := do
  if s.core.thread.status != .running then throw (.integer .blocked)
  let instruction ← require (code[s.core.thread.pc]?) (.integer (.invalidPC s.core.thread.pc))
  match instruction with
  | .integer i =>
      match i with
      | .load .. => match oracle s.core.queries with
        | .integer _ => pure ()
        | .real _ _ => throw (.oracleType s.core.queries)
      | _ => pure ()
      let result ← liftInteger (Event.step ctx.toContext (integerOracle oracle) (integerSkeleton code) s.core)
      return (finishInteger s result.1,result.2.map liftKind)
  | .setpGt format dst a b =>
      let x ← eval format s a
      let y ← eval format s b
      return (finishInteger s {s.core with thread := assign s.core.thread dst (if y < x then 1 else 0)},[])
  | .readSpecial dst source =>
      return (finishInteger s {s.core with thread := assign s.core.thread dst (wrap 32 (source.value ctx))},[])
  | .atomAddU32 dst address increment =>
      let addr ← liftInteger (evalAddr ctx.id.tid.x s.core.thread address)
      let addend ← liftInteger (Ptx.eval ctx.id.tid.x s.core.thread increment)
      match oracle s.core.queries with
      | .real _ _ => throw (.oracleType s.core.queries)
      | .integer value =>
          let old := wrap 32 value
          let next := finishInteger s {s.core with thread := assign s.core.thread dst old,queries := s.core.queries+1}
          return (next,[.rmw .gpu (Location.resolve .global ctx.id addr)
            (atomicAddBytes value addend)])
  | .mov format dst src => return (writeFloat s dst format (← eval format s src),[])
  | .addRn format dst a b =>
      let x ← eval format s a
      let y ← eval format s b
      return (writeFloat s dst format (x+y),[])
  | .subRn format dst a b =>
      let x ← eval format s a
      let y ← eval format s b
      return (writeFloat s dst format (x-y),[])
  | .mulRn format dst a b =>
      let x ← eval format s a
      let y ← eval format s b
      return (writeFloat s dst format (x*y),[])
  | .divRn format dst a b =>
      let x ← eval format s a
      let y ← eval format s b
      if y = 0 then throw .zeroDivisor
      return (writeFloat s dst format (x/y),[])
  | .max format dst a b =>
      let x ← eval format s a
      let y ← eval format s b
      return (writeFloat s dst format (max x y),[])
  | .ex2Approx dst src =>
      return (writeFloat s dst .f32 (RealMath.exp2 (← eval .f32 s src)),[])
  | .fmaRn format dst a b c =>
      let x ← eval format s a
      let y ← eval format s b
      let z ← eval format s c
      return (writeFloat s dst format (x*y+z),[])
  | .load format space dst address =>
      let addr ← liftInteger (evalAddr ctx.id.tid.x s.core.thread address)
      match oracle s.core.queries with
      | .integer _ => throw (.oracleType s.core.queries)
      | .real actual value =>
          if actual = format then
            let next := writeFloat s dst format value
            return ({next with core := {next.core with queries := s.core.queries+1}},
              [.read (Location.resolve space ctx.id addr) (Symbolic.encode format value)])
          else throw (.oracleType s.core.queries)
  | .store format space address value =>
      let addr ← liftInteger (evalAddr ctx.id.tid.x s.core.thread address)
      let x ← eval format s value
      return ({s with core := {s.core with thread := advance s.core.thread}},
        [.write (Location.resolve space ctx.id addr) (Symbolic.encode format x)])

def run (ctx : Context) (oracle : Oracle) (code : List Instr) : Nat → State → Except Fault (State × List Kind)
  | 0,s => .ok (s,[])
  | n+1,s => (step ctx oracle code s).bind fun first =>
      (run ctx oracle code n first.1).bind fun rest => .ok (rest.1,first.2 ++ rest.2)

theorem run_add (ctx : Context) (oracle : Oracle) (code : List Instr) (n m : Nat) (s : State) :
    run ctx oracle code (n+m) s = (run ctx oracle code n s).bind (fun first =>
      (run ctx oracle code m first.1).bind (fun last => .ok (last.1,first.2 ++ last.2))) := by
  induction n generalizing s with
  | zero => cases hr : run ctx oracle code m s <;> simp [run,hr,Except.bind]
  | succ n ih =>
    cases hs : step ctx oracle code s with
    | error fault => simp [Nat.succ_add,run,hs,Except.bind]
    | ok first =>
      rcases first with ⟨mid,events⟩
      rw [Nat.succ_add,run,hs]
      simp only [Except.bind]
      rw [ih]
      cases hr : run ctx oracle code n mid with
      | error fault => simp [run,hs,hr,Except.bind]
      | ok result =>
        rcases result with ⟨next,rest⟩
        simp [run,hs,hr,Except.bind]
        cases run ctx oracle code m next <;> rfl

theorem integer_local_step {ctx oracle code s instruction next}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.integer instruction)) (hl : isLocal instruction = true)
    (hb : ∀ bid, instruction ≠ .barrier bid)
    (hs : localStep ctx.params ctx.id.tid.x s.core.thread instruction = .ok next) :
    step ctx oracle code s = .ok (finishInteger s {s.core with thread := next},[]) := by
  have hfetch : (integerSkeleton code)[s.core.thread.pc]? = some instruction := by
    simp [integerSkeleton,List.getElem?_map,hc]
  have hlocal := Event.local_step (ctx := ctx.toContext) (oracle := integerOracle oracle) hr hfetch hl hb hs
  cases instruction <;> simp_all [isLocal]
  all_goals simp [step,hr,hc,require,hlocal,liftInteger,bind,Except.bind,pure,Except.pure]

theorem integer_load_step {ctx oracle code s space dst address addr value}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.integer (.load space dst address)))
    (ha : evalAddr ctx.id.tid.x s.core.thread address = .ok addr)
    (ho : oracle s.core.queries = .integer value) :
    step ctx oracle code s = .ok
      (finishInteger s {s.core with thread := assign s.core.thread dst (wrap 32 value),queries := s.core.queries+1},
        [.read (Location.resolve space ctx.id addr) ((encodeU32 (wrap 32 value)).map Symbolic.Byte.bits)]) := by
  simp [step,hr,hc,require,liftInteger,Event.step,integerSkeleton,List.getElem?_map,hc,
    ha,ho,integerOracle,liftKind,bind,Except.bind,pure,Except.pure]

theorem integer_store_step {ctx oracle code s space address operand addr value}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.integer (.store space address operand)))
    (ha : evalAddr ctx.id.tid.x s.core.thread address = .ok addr)
    (hv : Ptx.eval ctx.id.tid.x s.core.thread operand = .ok value) :
    step ctx oracle code s = .ok
      (finishInteger s {s.core with thread := advance s.core.thread},
        [.write (Location.resolve space ctx.id addr) ((encodeU32 value).map Symbolic.Byte.bits)]) := by
  simp [step,hr,hc,require,liftInteger,Event.step,integerSkeleton,List.getElem?_map,hc,
    ha,hv,liftKind,bind,Except.bind,pure,Except.pure]

def embedState (s : Event.State) : State := ⟨s,[]⟩
def embedOracle (oracle : Event.Oracle) : Oracle := fun query => .integer (oracle query)
@[simp] theorem integerOracle_embed (oracle : Event.Oracle) : integerOracle (embedOracle oracle) = oracle := rfl
def embedResult : Except Ptx.Fault (Event.State × List Event.Kind) → Except Fault (State × List Kind)
  | .error fault => .error (.integer fault)
  | .ok (s,events) => .ok (embedState s,events.map liftKind)

theorem step_integer (ctx : Event.Context) (oracle : Event.Oracle) (code : List Ptx.Instr) (s : Event.State) :
    step ctx (embedOracle oracle) (code.map Instr.integer) (embedState s) = embedResult (Event.step ctx oracle code s) := by
  have hcode : integerSkeleton (code.map Instr.integer) = code := by
    simp [integerSkeleton,List.map_map,Function.comp_def]
  by_cases hr : s.thread.status = .running
  · cases hc : code[s.thread.pc]? with
    | none => simp [step,embedState,Event.step,require,hr,List.getElem?_map,hc,embedResult,bind,Except.bind]
    | some instruction =>
      cases he : Event.step ctx oracle code s with
      | error fault =>
        cases instruction <;>
          simp [step,embedState,embedOracle,require,hr,List.getElem?_map,hc,hcode,
            he,liftInteger,embedResult,bind,Except.bind]
      | ok result =>
        rcases result with ⟨next,events⟩
        cases instruction <;>
          simp [step,embedState,embedOracle,require,hr,List.getElem?_map,hc,hcode,
            he,liftInteger,finishInteger,embedResult,bind,Except.bind,pure,Except.pure]
  · simp [step,embedState,Event.step,hr,embedResult,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

theorem run_integer (ctx : Event.Context) (oracle : Event.Oracle) (code : List Ptx.Instr) (n : Nat) (s : Event.State) :
    run ctx (embedOracle oracle) (code.map Instr.integer) n (embedState s) = embedResult (Event.run ctx oracle code n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [run,Event.run,step_integer]
    cases hs : Event.step ctx oracle code s with
    | error fault => simp [embedResult,Except.bind]
    | ok result =>
      rcases result with ⟨next,events⟩
      simp only [embedResult,Except.bind,ih]
      cases ht : Event.run ctx oracle code n next with
      | error fault => rfl
      | ok result =>
        rcases result with ⟨last,tail⟩
        simp only [List.map_append]

inductive Runs (ctx : Context) (oracle : Oracle) (code : List Instr) : State → List Kind → State → Prop
  | nil (s) : Runs ctx oracle code s [] s
  | cons {s mid last first rest} : step ctx oracle code s = .ok (mid,first) →
      Runs ctx oracle code mid rest last → Runs ctx oracle code s (first ++ rest) last

theorem run_sound {ctx oracle code n s last events} (h : run ctx oracle code n s = .ok (last,events)) :
    Runs ctx oracle code s events last := by
  induction n generalizing s last events with
  | zero =>
    simp only [run,Except.ok.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact .nil _
  | succ n ih =>
    cases hs : step ctx oracle code s with
    | error fault => simp [run,hs,Except.bind] at h
    | ok first =>
      rcases first with ⟨mid,head⟩
      cases ht : run ctx oracle code n mid with
      | error fault => simp [run,hs,ht,Except.bind] at h
      | ok tail =>
        rcases tail with ⟨last',rest⟩
        simp only [run,hs,ht,Except.bind,Except.ok.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact .cons hs (ih ht)

theorem run_after_done {ctx oracle code s} (hd : s.core.thread.status = .done) :
    step ctx oracle code s = .error (.integer .blocked) := by
  simp [step,hd,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

theorem liftKind_barrier {kind : Event.Kind} {bid generation : Nat}
    (hk : Event.BarrierKind bid generation (liftKind kind)) : Event.BarrierKind bid generation kind := by
  cases kind <;> simpa [Event.BarrierKind,liftKind] using hk

/-- A scalar barrier event comes from the actual integer barrier at the same PC.
Float operations, special-register reads and atomic RMWs cannot manufacture it.
The private integer skeleton is used only to justify this delegated step. -/
theorem step_barrier_source {ctx oracle code s next emitted kind bid generation}
    (hs : step ctx oracle code s = .ok (next,emitted)) (hm : kind ∈ emitted)
    (hk : Event.BarrierKind bid generation kind) :
    code[s.core.thread.pc]? = some (.integer (.barrier bid)) := by
  have hr : s.core.thread.status = .running := by
    by_cases h : s.core.thread.status = .running
    · exact h
    · simp [step,h,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs
  cases hc : code[s.core.thread.pc]? with
  | none => simp [step,hr,hc,require,bind,Except.bind] at hs
  | some instruction =>
    cases instruction with
    | integer instruction =>
      have hfetch : (integerSkeleton code)[s.core.thread.pc]? = some instruction := by
        simp [integerSkeleton,List.getElem?_map,hc]
      cases he : Event.step ctx.toContext (integerOracle oracle) (integerSkeleton code) s.core with
      | error fault =>
        cases instruction <;> cases ho : oracle s.core.queries <;>
          simp [step,hr,hc,require,he,ho,liftInteger,bind,Except.bind,pure,Except.pure] at hs
      | ok result =>
        rcases result with ⟨mid,events⟩
        cases instruction <;> cases ho : oracle s.core.queries <;>
          simp [step,hr,hc,require,he,ho,liftInteger,bind,Except.bind,pure,Except.pure] at hs
        all_goals
          rcases hs with ⟨rfl,rfl⟩
          obtain ⟨old,hmem,rfl⟩ := List.mem_map.mp hm
          have hb := Event.step_barrier_source he hmem (liftKind_barrier hk)
          rw [hfetch] at hb
          have hi := Option.some.inj hb
          cases hi
          all_goals rfl
    | _ =>
      simp [step,hr,hc,require,liftInteger,bind,Except.bind,pure,Except.pure,Except.map] at hs
      all_goals repeat' split at hs
      all_goals simp_all [Event.BarrierKind]
      all_goals rcases hs with ⟨_,rfl⟩
      all_goals simp_all

end
end Ptx.Scalar
