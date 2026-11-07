import Ptx.Hopper.MbarrierPrefixAccounting

/-! Phase monotonicity within a checked object lifetime. A reset is not silently
treated as monotone: the single-initialization inventory excludes it between
the two live prefixes. No bound on the number of intervening operations is used. -/
namespace Ptx.Hopper.Mbarrier
open Ptx.ISA

theorem accept_live_phase_mono {s next} (h : accept s = some (some next)) : s.phase ≤ next.phase := by
  unfold accept at h
  split at h
  · cases h
    rw [finish_phase]
    split <;> omega
  · cases h

theorem step_live_phase_mono {s op next} (h : step (some s) op = some (some next)) : s.phase ≤ next.phase := by
  cases op with
  | init n => cases h
  | inval => cases h
  | arriveExpectTx n =>
    simp only [step] at h
    split at h
    · have hm := accept_live_phase_mono h
      exact hm
    · cases h
  | completeTx n =>
    simp only [step] at h
    split at h
    · have hm := accept_live_phase_mono h
      exact hm
    · cases h
  | tryWaitParity p done =>
    simp only [step] at h
    split at h
    · split at h
      · cases h
        exact Nat.le_refl _
      · cases h
    · cases h
      exact Nat.le_refl _

theorem no_live_run_without_initialization {ops state}
    (hn : ∀ op ∈ ops, isInitialization op = false) : run none ops ≠ some (some state) := by
  cases ops with
  | nil => simp [run]
  | cons op rest =>
    have hh := hn op (by simp)
    cases op <;> simp_all [run,step,isInitialization]

theorem run_live_phase_mono {ops state next}
    (hn : ∀ op ∈ ops, isInitialization op = false) (hr : run (some state) ops = some (some next)) :
    state.phase ≤ next.phase := by
  induction ops generalizing state with
  | nil => cases hr; exact Nat.le_refl _
  | cons op rest ih =>
    have htail : ∀ x ∈ rest, isInitialization x = false := fun x hx => hn x (by simp [hx])
    cases he : step (some state) op with
    | none => simp [run,he] at hr
    | some mid =>
      have ht : run mid rest = some (some next) := by simpa only [run,he,Option.bind_some] using hr
      cases mid with
      | none => exact (no_live_run_without_initialization htail ht).elim
      | some mid => exact (step_live_phase_mono he).trans (ih htail ht)

theorem run_between_prefixes {ops : List BarrierOp} {first last : Nat} {before after}
    (hl : first ≤ last) (hb : run none (ops.take first) = some before) (ha : run none (ops.take last) = some after) :
    run before ((ops.drop first).take (last-first)) = some after := by
  have he : first+(last-first) = last := by omega
  have hd : (ops.take last).drop first = (ops.drop first).take (last-first) := by
    simpa only [he] using (List.take_drop (l := ops) (i := last-first) (j := first)).symm
  have hs := List.take_append_drop first (ops.take last)
  rw [List.take_take,Nat.min_eq_left hl,hd] at hs
  rw [← hs,run_append,hb,Option.bind_some] at ha
  exact ha

theorem single_initialization_phase_mono {ops last firstIndex lastIndex before after}
    (hi : (ops.filter isInitialization).length = 1)
    (hu : ∀ op ∈ ops, UnitInitialization op) (hr : run none ops = some last)
    (hl : firstIndex ≤ lastIndex)
    (hb : run none (ops.take firstIndex) = some (some before))
    (ha : run none (ops.take lastIndex) = some (some after)) : before.phase ≤ after.phase := by
  have hsegment := run_between_prefixes hl hb ha
  apply run_live_phase_mono ?_ hsegment
  obtain ⟨rest,he,hrest⟩ := single_initialization_shape hi hu hr
  cases firstIndex with
  | zero => simp [run] at hb
  | succ firstIndex =>
    intro op hop
    have hm := List.mem_of_mem_take hop
    rw [he,List.drop_succ_cons] at hm
    exact hrest op (List.mem_of_mem_drop hm)

end Ptx.Hopper.Mbarrier
