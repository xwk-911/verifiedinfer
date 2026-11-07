import Ptx.Scalar.RegisterFrame

/-! Ordered comparison in the finite exact-real fragment. No NaN/IEEE claim is
made. The predicate goes to the integer bank with cross-bank invalidation; the
remaining registers obey the same frame rules as other scalar assignments. -/
namespace Ptx.Scalar
open Ptx.ISA
noncomputable section

def gtFlag (x y : ℝ) : Nat := if y < x then 1 else 0

theorem gt_flag_bound (x y : ℝ) : gtFlag x y < 2 := by
  unfold gtFlag
  split <;> decide
theorem gt_flag_one {x y : ℝ} (h : y < x) : gtFlag x y = 1 := by simp [gtFlag,h]
theorem gt_flag_zero {x y : ℝ} (h : x ≤ y) : gtFlag x y = 0 := by simp [gtFlag,not_lt.mpr h]
theorem gt_flag_tie (x : ℝ) : gtFlag x x = 0 := gt_flag_zero (le_refl x)

theorem setp_gt_step {ctx oracle code s format dst a b x y}
    (hr : s.core.thread.status = .running)
    (hc : code[s.core.thread.pc]? = some (.setpGt format dst a b))
    (ha : eval format s a = .ok x) (hb : eval format s b = .ok y) :
    step ctx oracle code s = .ok (intAssign s dst (gtFlag x y),[]) := by
  simp [step,hr,hc,require,ha,hb,intAssign,gtFlag,bind,Except.bind,pure,Except.pure]

theorem setp_gt_banks (s : State) (dst : String) (x y : ℝ) : BanksDisjoint (intAssign s dst (gtFlag x y)) :=
  intAssign_banks _ _ _
theorem setp_gt_frame {s : State} (hi : BanksDisjoint s) (dst : String) (x y : ℝ) :
    RegisterFrame [dst] s (intAssign s dst (gtFlag x y)) := intAssign_register_frame hi _ _ (by simp)

end
end Ptx.Scalar
