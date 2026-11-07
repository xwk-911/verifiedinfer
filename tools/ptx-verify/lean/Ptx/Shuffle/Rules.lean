import Ptx.Shuffle.Execution

/-! Local selection/generation facts and actual source-step rules. Register
value and predicate agreement across lanes remains a global obligation.
-/
namespace Ptx.Shuffle
open Ptx.ISA
noncomputable section

theorem selected_lane_bounded (mode : Mode) (lane : Lane) (b c : Nat) : (select mode lane b c).source.toNat < 32 :=
  (select mode lane b c).source.isLt

theorem invalid_selection_uses_own_lane {mode lane b c} (hp : (select mode lane b c).predicate = false) :
    (select mode lane b c).source = lane := by
  cases mode <;> dsimp [select] at hp ⊢ <;> split <;> simp_all

theorem up_underflow_is_not_saturating (lane : Lane) (b c : Nat) (hb : lane.toNat < (BitVec.ofNat 5 b).toNat) :
    select .up lane b c = ⟨lane,false⟩ := by
  let bound := (lane &&& BitVec.ofNat 5 (c/256)) ||| (BitVec.ofNat 5 c &&& ~~~(BitVec.ofNat 5 (c/256)))
  have hn : ¬(bound.toNat : Int) ≤ (lane.toNat : Int) - ((BitVec.ofNat 5 b).toNat : Int) := by omega
  change (if (bound.toNat : Int) ≤ (lane.toNat : Int) - ((BitVec.ofNat 5 b).toNat : Int) then _ else _) = _
  simp only [hn,ite_false]

theorem offset_high_bits_ignored (mode : Mode) (lane : Lane) (b c k : Nat) : select mode lane (b+32*k) c = select mode lane b c := by
  have he : BitVec.ofNat 5 (b+32*k) = BitVec.ofNat 5 b := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat,Nat.add_mod]
  simp only [select,he]

theorem empty_generation (key : Key) : generation ({} : State) key = 0 := rfl
theorem generation_advance_same (state : State) (key : Key) : generation {state with visits := advanceVisits state key} key = generation state key+1 := by
  simp [generation,advanceVisits]

theorem generation_advance_other (state : State) (key other : Key) (hne : key ≠ other) :
    generation {state with visits := advanceVisits state key} other = generation state other := by
  have hf : (state.visits.filter (fun item => item.1 != key)).find? (fun item => item.1 == other) =
      state.visits.find? (fun item => item.1 == other) := by
    induction state.visits with
    | nil => rfl
    | cons head rest ih =>
      by_cases hk : head.1 = key
      · subst hk
        simp [hne,ih]
      · by_cases ho : head.1 = other
        · simp [ho,Ne.symm hne]
        · simp [hk,ho,ih]
  simp [generation,advanceVisits,hne,hf]

theorem writeResult_advances_once (state : Scalar.State) (dst : String) (predicate : Option String) (value : Nat) (valid : Bool) :
    (writeResult state dst predicate value valid).core.thread.pc = state.core.thread.pc+1 := by cases predicate <;> rfl

theorem shfl_step {ctx oracle code state mode dst predicate a b c mask input offset clamp participants}
    (hs : state.base.core.thread.status = .running) (hi : code[state.base.core.thread.pc]? = some (.shfl mode dst predicate a b c mask))
    (ha : Ptx.eval ctx.id.tid.x state.base.core.thread a = .ok input)
    (hb : Ptx.eval ctx.id.tid.x state.base.core.thread b = .ok offset)
    (hc : Ptx.eval ctx.id.tid.x state.base.core.thread c = .ok clamp)
    (hm : Ptx.eval ctx.id.tid.x state.base.core.thread mask = .ok participants) :
    step ctx oracle code state = .ok
      (⟨writeResult state.base dst predicate (oracle.shuffle state.queries).1 (oracle.shuffle state.queries).2,state.queries+1,
        advanceVisits state ⟨mode,wrap 32 participants⟩⟩,
        [.shuffle ⟨⟨mode,wrap 32 participants⟩,generation state ⟨mode,wrap 32 participants⟩,state.base.core.thread.pc,
          wrap 32 input,wrap 32 offset,wrap 32 clamp,wrap 32 (oracle.shuffle state.queries).1,(oracle.shuffle state.queries).2⟩]) := by
  simp [step,hs,Scalar.require,hi,ha,hb,hc,hm,Scalar.liftInteger,bind,Except.bind,Pure.pure,Except.pure]

end
end Ptx.Shuffle
