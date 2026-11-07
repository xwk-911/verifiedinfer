import Ptx.Generated.ShufflePair
import Ptx.Shuffle.Rules

/-! A mechanically translated two-lane register exchange. Arbitrary local
oracle values and predicates produce complete source traces; global shuffle
agreement, definedness and control are checked separately. The fixture exports
no memory result and may be optimized away by ptxas; the four exported probes
supply separate finite GPU evidence.
-/
namespace Ptx.Kernels.ShufflePair
open Ptx.ISA Ptx.Shuffle
noncomputable section

abbrev Lane2 := Fin 2
def id (lane : Lane2) : ThreadId := ⟨.zero,⟨lane.val,0,0⟩⟩
def block : Dim3 := ⟨2,1,1⟩
def key : Key := ⟨.bfly,3⟩
def oracle (value : Nat) (predicate : Bool) : Oracle := ⟨fun _ => .integer 0,fun _ => (value,predicate)⟩
def record (lane : Lane2) (value : Nat) (predicate : Bool) : Record := ⟨key,0,1,lane.val,1,31,wrap 32 value,predicate⟩
def finalState (lane : Lane2) (value : Nat) (predicate : Bool) : Shuffle.State := {
  base := {core := {thread := {pc := 2,regs := put "%p" (if predicate then 1 else 0) (put "%dst" (wrap 32 value) (put "%src" lane.val [])),status := .done}}}
  queries := 1
  visits := [(key,1)]
}
def trace (lane : Lane2) (value : Nat) (predicate : Bool) : Shuffle.ThreadTrace :=
  ⟨id lane,oracle value predicate,3,finalState lane value predicate,[.shuffle (record lane value predicate)]⟩
def candidate (a b : Nat) (pa pb : Bool) : Shuffle.Candidate := ⟨[trace 0 a pa,trace 1 b pb]⟩
def launch (initial : Location → Symbolic.Byte) : Scalar.Launch := ⟨⟨.one,block⟩,[],initial⟩
def event (lane : Lane2) : Ptx.Event.EventId := ⟨id lane,0⟩

theorem actual_source_run (lane : Lane2) (value : Nat) (predicate : Bool) :
    Shuffle.run {id := id lane,block := block} (oracle value predicate) Generated.shuffle_pair.program 3 {} =
      .ok (finalState lane value predicate,[.shuffle (record lane value predicate)]) := by
  fin_cases lane <;> rfl

theorem actual_source_produced (lane : Lane2) (value : Nat) (predicate : Bool) :
    Shuffle.Produced Generated.shuffle_pair.program [] block (trace lane value predicate) := actual_source_run lane value predicate

theorem actual_source_complete (a b : Nat) (pa pb : Bool) : Shuffle.Complete (candidate a b pa pb) := by
  intro actual ht
  simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl

theorem actual_source_well_formed (a b : Nat) (pa pb : Bool) (initial : Location → Symbolic.Byte) :
    Shuffle.WellFormed Generated.shuffle_pair.program (launch initial) (candidate a b pa pb) := by
  refine ⟨by simp [launch,block,Geometry.Valid,Dim3.Positive,Dim3.one],by simp [candidate,trace,id],?_,?_⟩
  · intro actual ht
    simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨by simp [trace,id,launch,block,ThreadId.Valid,Dim3.Within,Dim3.one,Dim3.zero],actual_source_produced 0 a pa⟩
    · exact ⟨by simp [trace,id,launch,block,ThreadId.Valid,Dim3.Within,Dim3.one,Dim3.zero],actual_source_produced 1 b pb⟩
  · intro thread ht
    rcases thread with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
    simp only [ThreadId.Valid,launch,block,Dim3.Within,Dim3.one] at ht
    have hcx : cx = 0 := by omega
    have hcy : cy = 0 := by omega
    have hcz : cz = 0 := by omega
    have hty : ty = 0 := by omega
    have htz : tz = 0 := by omega
    subst cx; subst cy; subst cz; subst ty; subst tz
    have hx : tx = 0 ∨ tx = 1 := by omega
    rcases hx with rfl | rfl
    · exact ⟨trace 0 a pa,by simp [candidate],rfl⟩
    · exact ⟨trace 1 b pb,by simp [candidate],rfl⟩

theorem lookup_zero (a b : Nat) (pa pb : Bool) : (candidate a b pa pb).shuffleAt (event 0) = some (record 0 a pa) := rfl
theorem lookup_one (a b : Nat) (pa pb : Bool) : (candidate a b pa pb).shuffleAt (event 1) = some (record 1 b pb) := rfl

theorem event_cases {a b pa pb actual kind} (he : (candidate a b pa pb).eventAt actual = some kind) :
    (actual = event 0 ∧ kind = .shuffle (record 0 a pa)) ∨ (actual = event 1 ∧ kind = .shuffle (record 1 b pb)) := by
  unfold Shuffle.Candidate.eventAt at he
  cases hf : (candidate a b pa pb).traces.find? (fun t => t.id == actual.thread) with
  | none => simp [hf] at he
  | some t =>
    have hm := List.mem_of_find?_eq_some hf
    have hid : t.id = actual.thread := by simpa only [beq_iff_eq] using List.find?_some (p := fun t : Shuffle.ThreadTrace => t.id == actual.thread) hf
    simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    all_goals
      simp only [hf,Option.bind_some,trace] at he
      cases actual with
      | mk thread serial =>
        cases serial with
        | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at he
          dsimp only [trace] at hid
          subst thread; subst kind
          first | exact Or.inl ⟨rfl,rfl⟩ | exact Or.inr ⟨rfl,rfl⟩
        | succ serial => simp at he

theorem shuffle_cases {a b pa pb actual result} (he : (candidate a b pa pb).shuffleAt actual = some result) :
    (actual = event 0 ∧ result = record 0 a pa) ∨ (actual = event 1 ∧ result = record 1 b pb) := by
  unfold Shuffle.Candidate.shuffleAt at he
  cases hx : (candidate a b pa pb).eventAt actual with
  | none => simp [hx] at he
  | some kind =>
    obtain (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) := event_cases hx
    · exact Or.inl ⟨rfl,Option.some.inj he.symm⟩
    · exact Or.inr ⟨rfl,Option.some.inj he.symm⟩

end
end Ptx.Kernels.ShufflePair
