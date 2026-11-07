import Ptx.Kernels.ShufflePairAgreement
import Ptx.Generated.ShuffleUp
import Ptx.Generated.ShuffleDown
import Ptx.Generated.ShuffleBfly
import Ptx.Generated.ShuffleIdx

/-! Selection, generation and actual source/global agreement regressions.
Finite selection checks are distinct from the parameterized source proofs. -/
namespace Ptx.ShuffleTests
open Ptx.ISA Ptx.Shuffle
open Ptx.Kernels.ShufflePair
noncomputable section

theorem all_four_generated_probes_typed :
    Shuffle.ProgramTyped 70 Generated.shuffle_up.registerDeclarations Generated.shuffle_up.parameters Generated.shuffle_up.program ∧
    Shuffle.ProgramTyped 70 Generated.shuffle_down.registerDeclarations Generated.shuffle_down.parameters Generated.shuffle_down.program ∧
    Shuffle.ProgramTyped 70 Generated.shuffle_bfly.registerDeclarations Generated.shuffle_bfly.parameters Generated.shuffle_bfly.program ∧
    Shuffle.ProgramTyped 70 Generated.shuffle_idx.registerDeclarations Generated.shuffle_idx.parameters Generated.shuffle_idx.program :=
  ⟨Generated.shuffle_up.checked.valid,Generated.shuffle_down.checked.valid,
    Generated.shuffle_bfly.checked.valid,Generated.shuffle_idx.checked.valid⟩

theorem up_underflow_returns_own_input : select .up 0 1 0 = ⟨0,false⟩ := by decide
theorem up_lower_clamp_is_respected : select .up 16 1 0x1000 = ⟨16,false⟩ := by decide
theorem down_overflow_returns_own_input : select .down 31 1 31 = ⟨31,false⟩ := by decide
theorem down_segment_boundary_is_respected : select .down 15 1 0x100f = ⟨15,false⟩ := by decide
theorem bfly_can_select_lower_segment : select .bfly 16 16 0x100f = ⟨0,true⟩ := by decide
theorem bfly_same_segment_exchange : select .bfly 17 1 0x100f = ⟨16,true⟩ := by decide
theorem idx_segment_preserves_high_bit : select .idx 17 20 0x100f = ⟨20,true⟩ := by decide
theorem idx_clamp_failure_returns_self : select .idx 17 31 15 = ⟨17,false⟩ := by decide
theorem idx_high_b_bits_are_ignored : select .idx 0 39 31 = ⟨7,true⟩ := by decide
theorem c_reserved_bits_are_ignored : select .idx 3 7 0xffffe0ff = select .idx 3 7 31 := by decide

theorem repeated_key_advances_generation :
    generation {visits := advanceVisits {visits := advanceVisits {} key} key : State} key = 2 := by decide
theorem other_mode_does_not_advance_generation :
    generation {visits := advanceVisits {} key : State} ⟨.idx,3⟩ = 0 := by decide
theorem other_mask_does_not_advance_generation :
    generation {visits := advanceVisits {} key : State} ⟨.bfly,7⟩ = 0 := by decide

theorem correct_pair_is_a_complete_source_witness (initial : Location → Symbolic.Byte) :
    WellFormed Generated.shuffle_pair.program (launch initial) (candidate 1 0 true true) ∧
    Complete (candidate 1 0 true true) ∧ ControlAdmitted block (candidate 1 0 true true) ∧
    Defined block (candidate 1 0 true true) ∧ Agreement block (candidate 1 0 true true) := pair_legal_complete_witness initial

theorem arbitrary_local_replies_still_have_source_runs (a b : Nat) (pa pb : Bool) (initial : Location → Symbolic.Byte) :
    WellFormed Generated.shuffle_pair.program (launch initial) (candidate a b pa pb) ∧ Complete (candidate a b pa pb) :=
  ⟨actual_source_well_formed a b pa pb initial,actual_source_complete a b pa pb⟩

theorem wrong_value_has_no_global_agreement : ¬Agreement block (candidate 0 0 true true) := by
  intro ha
  have hx := ((pair_agreement_iff 0 0 true true).1 ha).1
  exact Nat.zero_ne_one hx

theorem wrong_predicate_has_no_global_agreement : ¬Agreement block (candidate 1 0 false true) := by
  intro ha
  have hx := ((pair_agreement_iff 1 0 false true).1 ha).2.1
  cases hx

theorem correct_pair_registers :
    lookup "%dst" (finalState 0 1 true).base.core.thread.regs = some 1 ∧
    lookup "%dst" (finalState 1 0 true).base.core.thread.regs = some 0 ∧
    lookup "%p" (finalState 0 1 true).base.core.thread.regs = some 1 ∧
    lookup "%p" (finalState 1 0 true).base.core.thread.regs = some 1 :=
  pair_register_correct ((pair_agreement_iff 1 0 true true).2 (by decide))

theorem shuffle_has_no_ordinary_memory_event :
    (candidate 1 0 true true).view.traces.all (fun trace => trace.events.isEmpty) = true := rfl

end
end Ptx.ShuffleTests
