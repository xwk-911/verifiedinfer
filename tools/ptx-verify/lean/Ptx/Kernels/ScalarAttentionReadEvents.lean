import Ptx.Kernels.ScalarAttentionReads

/-! Query/event indexing for arbitrary candidate-local attention reads. These
facts identify actual source events, not initial-memory values or consistency. -/
namespace Ptx.ScalarAttentionReads
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttentionOuter
noncomputable section

@[simp] theorem itemReads_length (l : Layout) (q key : Attention.Matrix) (value : Nat → ℝ)
    (j : Nat) (hj : j < l.keys) : (itemReads l q key value j hj).length = 2*l.dim+1 := by
  simp [itemReads,iterationReads,dotLayout]

@[simp] theorem reads_length (l : Layout) (q key : Attention.Matrix) (value : Nat → ℝ)
    (start count : Nat) (hb : start+count ≤ l.keys) :
    (reads l q key value start count).length = (2*l.dim+1)*count := by
  induction count generalizing start with
  | zero => rfl
  | succ n ih =>
    have hj : start < l.keys := by omega
    simp only [reads,dite_eq_left hj,List.length_append,itemReads_length,ih (start+1) (by omega)]
    simp only [Nat.mul_succ]
    omega

theorem item_q {l : Layout} {q key : Attention.Matrix} {value : Nat → ℝ} {j k : Nat}
    (hj : j < l.keys) (hk : k < l.dim) :
    (itemReads l q key value j hj)[2*k]? =
      some (.read ⟨.global,l.qBase+4*k⟩ (Symbolic.encode .f32 (q j k))) := by
  unfold itemReads iterationReads
  rw [List.getElem?_append_left (by simp; omega)]
  simpa only [dotLayout,Nat.zero_add] using ScalarAttentionDot.loopReads_q (l := dotLayout l j hj) (start := 0) hk

theorem item_key {l : Layout} {q key : Attention.Matrix} {value : Nat → ℝ} {j k : Nat}
    (hj : j < l.keys) (hk : k < l.dim) :
    (itemReads l q key value j hj)[2*k+1]? =
      some (.read ⟨.global,l.keyBase+4*l.dim*j+4*k⟩ (Symbolic.encode .f32 (key j k))) := by
  unfold itemReads iterationReads
  rw [List.getElem?_append_left (by simp; omega)]
  simpa only [dotLayout,Nat.zero_add] using ScalarAttentionDot.loopReads_key (l := dotLayout l j hj) (start := 0) hk

theorem item_value {l : Layout} {q key : Attention.Matrix} {value : Nat → ℝ} {j : Nat}
    (hj : j < l.keys) :
    (itemReads l q key value j hj)[2*l.dim]? =
      some (.read ⟨.global,l.valueBase+4*l.dim*j⟩ (Symbolic.encode .f32 (value j))) := by
  simp [itemReads,iterationReads,dotLayout]

theorem item_event {l : Layout} {q key : Attention.Matrix} {value : Nat → ℝ} {j serial : Nat}
    (hj : j < l.keys) {kind : Scalar.Kind} (he : (itemReads l q key value j hj)[serial]? = some kind) :
    (∃ k, k < l.dim ∧ kind = .read ⟨.global,l.qBase+4*k⟩ (Symbolic.encode .f32 (q j k))) ∨
    (∃ k, k < l.dim ∧ kind = .read ⟨.global,l.keyBase+4*l.dim*j+4*k⟩ (Symbolic.encode .f32 (key j k))) ∨
    kind = .read ⟨.global,l.valueBase+4*l.dim*j⟩ (Symbolic.encode .f32 (value j)) := by
  have hs := (List.getElem?_eq_some_iff.mp he).1
  rw [itemReads_length] at hs
  by_cases hdot : serial < 2*l.dim
  · unfold itemReads iterationReads at he
    rw [List.getElem?_append_left (by simpa using hdot)] at he
    obtain ⟨k,hk,hcases⟩ := ScalarAttentionDot.loopReads_event he
    rcases hcases with ⟨_,hkind⟩ | ⟨_,hkind⟩
    · exact .inl ⟨k,hk,by simpa only [dotLayout,Nat.zero_add] using hkind⟩
    · exact .inr (.inl ⟨k,hk,by simpa only [dotLayout,Nat.zero_add] using hkind⟩)
  · have hserial : serial = 2*l.dim := by omega
    rw [hserial,item_value hj] at he
    exact .inr (.inr (Option.some.inj he).symm)

theorem reads_at {l : Layout} {q key : Attention.Matrix} {value : Nat → ℝ} {start count j serial : Nat}
    (hb : start+count ≤ l.keys) (hj : j < count) (hs : serial < 2*l.dim+1) :
    (reads l q key value start count)[(2*l.dim+1)*j+serial]? =
      (itemReads l q key value (start+j) (by omega))[serial]? := by
  induction count generalizing start j with
  | zero => omega
  | succ n ih =>
    have hstart : start < l.keys := by omega
    rw [reads,dite_eq_left hstart]
    cases j with
    | zero =>
      simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_zero] using
        List.getElem?_append_left (l₁ := itemReads l q key value start hstart)
          (l₂ := reads l q key value (start+1) n) (by simpa only [itemReads_length] using hs)
    | succ j =>
      rw [List.getElem?_append_right (by simp only [itemReads_length,Nat.mul_succ]; omega),itemReads_length]
      have hsub : (2*l.dim+1)*(j+1)+serial-(2*l.dim+1) = (2*l.dim+1)*j+serial := by
        simp only [Nat.mul_succ]
        omega
      rw [hsub]
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using ih (start := start+1) (j := j) (by omega) (by omega)

theorem reads_event {l : Layout} {q key : Attention.Matrix} {value : Nat → ℝ} {start count serial : Nat}
    (hb : start+count ≤ l.keys) {kind : Scalar.Kind}
    (he : (reads l q key value start count)[serial]? = some kind) :
    ∃ j, start ≤ j ∧ j < start+count ∧ j < l.keys ∧
      ((∃ k, k < l.dim ∧ kind = .read ⟨.global,l.qBase+4*k⟩ (Symbolic.encode .f32 (q j k))) ∨
       (∃ k, k < l.dim ∧ kind = .read ⟨.global,l.keyBase+4*l.dim*j+4*k⟩ (Symbolic.encode .f32 (key j k))) ∨
       kind = .read ⟨.global,l.valueBase+4*l.dim*j⟩ (Symbolic.encode .f32 (value j))) := by
  induction count generalizing start serial with
  | zero => simp [reads] at he
  | succ n ih =>
    have hstart : start < l.keys := by omega
    rw [reads,dite_eq_left hstart] at he
    by_cases hs : serial < 2*l.dim+1
    · rw [List.getElem?_append_left (by simpa only [itemReads_length] using hs)] at he
      exact ⟨start,by omega,by omega,hstart,item_event hstart he⟩
    · rw [List.getElem?_append_right (by simp only [itemReads_length]; omega)] at he
      obtain ⟨j,hlo,hhi,hj,hkind⟩ := ih (by omega : start+1+n ≤ l.keys) he
      exact ⟨j,by omega,by omega,hj,hkind⟩

end
end Ptx.ScalarAttentionReads
