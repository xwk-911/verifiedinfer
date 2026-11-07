import Ptx.Hopper.ControlPresence
import Ptx.Hopper.PrefixExistence

/-! Full actual and bounded actual prefixes are reachable from the empty cut
under existing source-matched resource histories and strict control ranks.
No absent node is admitted merely because its rank happens to be small. -/
namespace Ptx.Hopper.Progress
open Ptx.ISA
noncomputable section

theorem full_prefix_reached {block resolve candidate histories}
    (hh : ∀ loc, Tma.HistoryValid resolve candidate.view loc (histories loc))
    (rank : Unified.ControlNode → Nat)
    (hr : ∀ before after, Unified.ControlEdge block candidate histories before after → rank before < rank after) :
    Reached block candidate histories (Present candidate) := by
  apply finite_valid_rank_reached (inventory candidate) (fun _ => present_mem_inventory) ?_ rank hr
  exact ⟨fun _ _ he _ => (control_edge_present hh he).1,fun _ h => h⟩

theorem actual_rank_prefix_reached {block resolve candidate histories}
    (hh : ∀ loc, Tma.HistoryValid resolve candidate.view loc (histories loc))
    (rank : Unified.ControlNode → Nat)
    (hr : ∀ before after, Unified.ControlEdge block candidate histories before after → rank before < rank after) (limit : Nat) :
    Reached block candidate histories (fun node => Present candidate node ∧ rank node < limit) := by
  apply finite_valid_rank_reached (inventory candidate) (fun _ h => present_mem_inventory h.1) ?_ rank hr
  exact ⟨fun _ _ he hd => ⟨(control_edge_present hh he).1,(hr _ _ he).trans hd.2⟩,fun _ h => h.1⟩

end
end Ptx.Hopper.Progress
