import Ptx.Hopper.MbarrierAccounting

/-! A full pending-arrival count cannot have positive outstanding transaction
credit in a valid protocol run. Completion debt is deliberately permitted by
the signed operational model; nonnegative credit requires actual matching. -/
namespace Ptx.Hopper.Mbarrier
open Ptx.ISA

def RestingNonpositive : Object → Prop
  | none => True
  | some s => s.pending = s.expected → s.tx ≤ 0

theorem finish_resting_nonpositive {s} (hs : RestingNonpositive (some s)) : RestingNonpositive (some (finish s)) := by
  unfold finish
  split
  · rename_i h
    intro _
    dsimp only
    omega
  · exact hs

theorem accept_resting_nonpositive {s next} (hs : RestingNonpositive (some s)) (h : accept s = some next) :
    RestingNonpositive next := by
  unfold accept at h
  split at h
  · cases h
    exact finish_resting_nonpositive hs
  · cases h

theorem step_resting_nonpositive {s op next} (hw : ObjectWellFormed s) (hs : RestingNonpositive s)
    (h : step s op = some next) : RestingNonpositive next := by
  cases s with
  | none =>
    cases op <;> simp only [step] at h <;> try cases h
    split at h
    · cases h
      simp [RestingNonpositive,initialized]
    · cases h
  | some s =>
    cases op with
    | init n => cases h
    | inval => cases h; trivial
    | arriveExpectTx n =>
      simp only [step] at h
      split at h
      · apply accept_resting_nonpositive ?_ h
        intro he
        have hbound := hw.2.2.1
        have hpositive := hw.1
        change s.pending-1 = s.expected at he
        omega
      · cases h
    | completeTx n =>
      simp only [step] at h
      split at h
      · apply accept_resting_nonpositive ?_ h
        intro he
        have hold := hs he
        have hn := Int.natCast_nonneg n
        change s.tx-(n : Int) ≤ 0
        omega
      · cases h
    | tryWaitParity p complete =>
      simp only [step] at h
      split at h
      · split at h
        · cases h
          exact hs
        · cases h
      · cases h
        exact hs

theorem run_resting_nonpositive_from {s ops next} (hw : ObjectWellFormed s) (hs : RestingNonpositive s)
    (h : run s ops = some next) : RestingNonpositive next := by
  induction ops generalizing s with
  | nil => cases h; exact hs
  | cons op rest ih =>
    cases he : step s op with
    | none => simp [run,he] at h
    | some mid =>
      have hr : run mid rest = some next := by simpa only [run,he,Option.bind_some] using h
      exact ih (step_wf hw he) (step_resting_nonpositive hw hs he) hr

theorem run_resting_nonpositive {ops next} (h : run none ops = some next) : RestingNonpositive next :=
  run_resting_nonpositive_from (s := none) trivial trivial h

end Ptx.Hopper.Mbarrier
