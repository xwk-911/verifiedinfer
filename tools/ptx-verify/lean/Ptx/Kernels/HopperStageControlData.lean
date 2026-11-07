import Ptx.Kernels.HopperStageResourceInventory
import Ptx.Hopper.TmaResourceRank

namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def sourceControlRank (id : Ptx.Event.EventId) : Nat :=
  let lane := id.thread.tid.linear block
  if lane = 0 then
    if id.serial ≤ 6 then 10*id.serial else if id.serial = 7 then 100+lane else 300+10*(id.serial-8)
  else if id.serial = 0 then 20 else if id.serial = 1 then 30 else if id.serial = 2 then 100+lane else 300+10*(id.serial-3)
def controlRank : Tma.Node → Nat
  | .source id => sourceControlRank id
  | .descriptor id => sourceControlRank id.issue+1
  | .read id _ => sourceControlRank id.issue+2
  | .write id _ => sourceControlRank id.issue+3
  | .notify id => sourceControlRank id.issue+4

theorem cta_tag_rank : ∀ id ∈ resourceCandidate.eventIds, ∀ arrival : Bool,
    ∀ tag ∈ (resourceCandidate.ctaTag arrival id).toList,
      sourceControlRank id = if arrival then (if tag.1 = 0 then 20 else 380) else (if tag.1 = 0 then 30 else 390) := by decide
theorem history_rank_pairwise : (resourceHistory.map Tma.Entry.origin).Pairwise (fun a b => controlRank a.node < controlRank b.node) := by decide

end
end Ptx.Kernels.HopperStage
