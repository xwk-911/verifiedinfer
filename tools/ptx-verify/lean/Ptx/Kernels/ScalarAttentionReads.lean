import Ptx.Kernels.ScalarAttentionOuter

/-! Local attention execution for arbitrary PER-ITEM Q read answers. The source
reads the same Q addresses each item; equality of those replies is a later memory
duty, not a premise of source reconstruction. Existing mathematical-input
execution remains a specialization of the same actual instruction rules. -/
namespace Ptx.ScalarAttentionReads
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttentionOuter
noncomputable section

def score (l : Layout) (q key : Attention.Matrix) (scale : ℝ) (item : Nat) : ℝ :=
  scale*Attention.dot q key item item l.dim

def itemReads (l : Layout) (q key : Attention.Matrix) (value : Nat → ℝ) (j : Nat) (hj : j < l.keys) : List Scalar.Kind :=
  iterationReads l q key (fun item _ => value item) j 0 j hj

def reads (l : Layout) (q key : Attention.Matrix) (value : Nat → ℝ) (start : Nat) : Nat → List Scalar.Kind
  | 0 => []
  | n+1 => if hj : start < l.keys then itemReads l q key value start hj ++ reads l q key value (start+1) n else []

theorem complete_suffix (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (q key : Attention.Matrix) (value : Nat → ℝ) (scale : ℝ) (hkeys : 0 < l.keys)
    (hq : ∀ j k, j < l.keys → k < l.dim → oracle (queryIndex l j+2*k) = .real .f32 (q j k))
    (hk : ∀ j k, j < l.keys → k < l.dim → oracle (queryIndex l j+2*k+1) = .real .f32 (key j k))
    (hv : ∀ j, j < l.keys → oracle (queryIndex l j+2*l.dim) = .real .f32 (value j))
    (remaining : Nat) :
    ∀ {start s}, l.keys = start+remaining → Inv l (score l q key scale) value scale start s →
      ∃ final, Scalar.run ctx oracle code (suffixSteps l.dim start remaining) s = .ok
        (final,reads l q key value start remaining ++
          [.write ⟨.global,l.output⟩ (Symbolic.encode .f32 (OnlineSoftmax.average (score l q key scale) value l.keys))]) ∧
        final.core.thread.status = .done := by
  induction remaining with
  | zero =>
    intro start s he hi
    have hs : start = l.keys := by omega
    subst start
    simpa only [suffixSteps,reads,List.nil_append] using finish l ctx oracle (score l q key scale) value scale hkeys hi
  | succ n ih =>
    intro start s he hi
    have hj : start < l.keys := by omega
    obtain ⟨mid,hr,hm,_⟩ := iteration_for_score l ctx oracle q key (fun item _ => value item)
      start 0 scale (score l q key scale) hi hj rfl (hq start · hj ·) (hk start · hj ·) (hv start hj)
    obtain ⟨final,ht,hf⟩ := ih (by omega : l.keys = (start+1)+n) hm
    refine ⟨final,?_,hf⟩
    rw [suffixSteps,Scalar.run_add,hr]
    simp only [Except.bind,ht,reads,dite_eq_left hj,itemReads,List.append_assoc]

theorem complete_from_entry (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (q key : Attention.Matrix) (value : Nat → ℝ) (scale : ℝ) (hkeys : 0 < l.keys)
    (hq : ∀ j k, j < l.keys → k < l.dim → oracle (queryIndex l j+2*k) = .real .f32 (q j k))
    (hk : ∀ j k, j < l.keys → k < l.dim → oracle (queryIndex l j+2*k+1) = .real .f32 (key j k))
    (hv : ∀ j, j < l.keys → oracle (queryIndex l j+2*l.dim) = .real .f32 (value j))
    {s} (hi : Inv l (score l q key scale) value scale 0 s) :
    ∃ final, Scalar.run ctx oracle code (l.keys*(9*l.dim+26)-2) s = .ok
      (final,reads l q key value 0 l.keys ++
        [.write ⟨.global,l.output⟩ (Symbolic.encode .f32 (OnlineSoftmax.average (score l q key scale) value l.keys))]) ∧
      final.core.thread.status = .done := by
  simpa only [suffixSteps_from_zero l.dim l.keys hkeys] using
    complete_suffix l ctx oracle q key value scale hkeys hq hk hv l.keys (by omega) hi

end
end Ptx.ScalarAttentionReads
