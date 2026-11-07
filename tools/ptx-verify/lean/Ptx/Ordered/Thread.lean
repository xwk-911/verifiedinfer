import Ptx.Ordered.Syntax
import Ptx.Scalar.Thread

/-! Source-driven order/scope annotations, retained on emitted memory events.
No runtime schedule or read value is fabricated. Consistency is separate. -/
namespace Ptx.Ordered
open Ptx.ISA
noncomputable section

inductive Order | weak | relaxed | acquire | release deriving Repr, DecidableEq
structure Kind where
  event : Scalar.Kind
  order : Order
  scope : Option Scope

def annotate (instruction : Instr) (event : Scalar.Kind) : Kind :=
  match instruction with
  | .scalar _ => ⟨event,.weak,none⟩
  | .load .relaxed scope _ _ => ⟨event,.relaxed,some scope⟩
  | .load .acquire scope _ _ => ⟨event,.acquire,some scope⟩
  | .store .relaxed scope _ _ => ⟨event,.relaxed,some scope⟩
  | .store .release scope _ _ => ⟨event,.release,some scope⟩

abbrev State := Scalar.State
abbrev Oracle := Scalar.Oracle

def step (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) (state : State) :
    Except Scalar.Fault (State × List Kind) :=
  (Scalar.require code[state.core.thread.pc]? (.integer (.invalidPC state.core.thread.pc))).bind fun instruction =>
    (Scalar.step ctx oracle (scalarSkeleton code) state).bind fun result =>
      .ok (result.1,result.2.map (annotate instruction))

def run (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) :
    Nat → State → Except Scalar.Fault (State × List Kind)
  | 0,state => .ok (state,[])
  | count+1,state =>
    (step ctx oracle code state).bind fun result =>
      (run ctx oracle code count result.1).bind fun tail => .ok (tail.1,result.2++tail.2)

inductive Runs (ctx : Scalar.Context) (oracle : Oracle) (code : List Instr) : State → List Kind → State → Prop
  | nil (state) : Runs ctx oracle code state [] state
  | cons {state next last first rest} : step ctx oracle code state = .ok (next,first) →
      Runs ctx oracle code next rest last → Runs ctx oracle code state (first++rest) last

theorem run_sound {ctx oracle code count state last events}
    (hr : run ctx oracle code count state = .ok (last,events)) : Runs ctx oracle code state events last := by
  induction count generalizing state last events with
  | zero =>
    simp only [run,Except.ok.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,rfl⟩ := hr
    exact .nil _
  | succ count ih =>
    cases hs : step ctx oracle code state with
    | error fault => simp [run,hs,Except.bind] at hr
    | ok result =>
      obtain ⟨next,first⟩ := result
      cases ht : run ctx oracle code count next with
      | error fault => simp [run,hs,ht,Except.bind] at hr
      | ok result =>
        obtain ⟨last',rest⟩ := result
        simp only [run,hs,ht,Except.bind,Except.ok.injEq,Prod.mk.injEq] at hr
        obtain ⟨rfl,rfl⟩ := hr
        exact .cons hs (ih ht)

theorem step_preserves_scalar_events {ctx oracle code state next events}
    (hs : step ctx oracle code state = .ok (next,events)) :
    Scalar.step ctx oracle (scalarSkeleton code) state = .ok (next,events.map Kind.event) := by
  unfold step at hs
  cases hi : code[state.core.thread.pc]? with
  | none => simp [hi,Scalar.require,Except.bind] at hs
  | some instruction =>
    cases hr : Scalar.step ctx oracle (scalarSkeleton code) state with
    | error fault => simp [hi,hr,Scalar.require,Except.bind] at hs
    | ok result =>
      obtain ⟨next',plain⟩ := result
      simp only [hi,Scalar.require,hr,Except.bind,Except.ok.injEq,Prod.mk.injEq] at hs
      obtain ⟨rfl,rfl⟩ := hs
      congr 2
      simp only [List.map_map]
      have he : Kind.event ∘ annotate instruction = id := by
        funext event
        cases instruction with
        | scalar => rfl
        | load order => cases order <;> rfl
        | store order => cases order <;> rfl
      rw [he,List.map_id]

theorem run_preserves_scalar_events {ctx oracle code count state last events}
    (hr : run ctx oracle code count state = .ok (last,events)) :
    Scalar.run ctx oracle (scalarSkeleton code) count state = .ok (last,events.map Kind.event) := by
  induction count generalizing state last events with
  | zero =>
    simp only [run,Except.ok.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,rfl⟩ := hr
    rfl
  | succ count ih =>
    cases hs : step ctx oracle code state with
    | error fault => simp [run,hs,Except.bind] at hr
    | ok result =>
      obtain ⟨next,first⟩ := result
      cases ht : run ctx oracle code count next with
      | error fault => simp [run,hs,ht,Except.bind] at hr
      | ok result =>
        obtain ⟨last',rest⟩ := result
        simp only [run,hs,ht,Except.bind,Except.ok.injEq,Prod.mk.injEq] at hr
        obtain ⟨rfl,rfl⟩ := hr
        rw [Scalar.run,step_preserves_scalar_events hs]
        simp only [Except.bind]
        rw [ih ht]
        simp only [Except.bind,List.map_append]

end
end Ptx.Ordered
