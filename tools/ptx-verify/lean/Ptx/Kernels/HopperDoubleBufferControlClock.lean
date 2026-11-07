import Ptx.Kernels.HopperDoubleBufferTmaAgreement

/-! A virtual clock for the chosen source witness. Missing producer final
prefetches and peer-only event strides are accounted for explicitly. Clock
order is a control proof device, not cross-proxy memory publication. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def producerThreshold (tiles : Nat) : Nat := if tiles = 0 then 5 else 10*tiles-1
def producerTick (tiles serial : Nat) : Nat := serial+(if producerThreshold tiles ≤ serial then 3 else 0)
def peerTick (tiles serial : Nat) : Nat :=
  if serial < 2 then serial+3 else
  if 2+7*tiles ≤ serial then 8+10*tiles+(serial-(2+7*tiles)) else
    8+10*((serial-2)/7)+(serial-2)%7+(if (serial-2)%7 = 0 then 0 else 3)
def sourceTick (tiles lane serial : Nat) : Nat := if lane = 0 then producerTick tiles serial else peerTick tiles serial
def sourceControlRank (tiles : Nat) (id : Ptx.Event.EventId) : Nat :=
  1024*sourceTick tiles (resourceLane id.thread) id.serial+resourceLane id.thread
def controlRank (tiles : Nat) : Tma.Node → Nat
  | .source id => sourceControlRank tiles id
  | .descriptor copy => sourceControlRank tiles copy.issue+128
  | .read copy _ => sourceControlRank tiles copy.issue+256
  | .write copy _ => sourceControlRank tiles copy.issue+384
  | .notify copy => sourceControlRank tiles copy.issue+512

theorem producer_tick_strict (tiles) : StrictMono (producerTick tiles) := by
  intro left right h
  simp only [producerTick]
  split_ifs <;> omega

theorem peer_tick_strict (tiles) : StrictMono (peerTick tiles) := by
  intro left right h
  simp only [peerTick]
  split_ifs <;> omega

theorem source_tick_strict (tiles lane) : StrictMono (sourceTick tiles lane) := by
  intro left right h
  by_cases hz : lane = 0
  · simpa only [sourceTick,hz,ite_true] using producer_tick_strict tiles h
  · simpa only [sourceTick,hz,ite_false] using peer_tick_strict tiles h

theorem source_control_strict (tiles) (left right : Ptx.Event.EventId)
    (ht : left.thread = right.thread) (hs : left.serial < right.serial) :
    sourceControlRank tiles left < sourceControlRank tiles right := by
  have he := source_tick_strict tiles (resourceLane left.thread) hs
  simp only [sourceControlRank,← ht]
  omega

theorem control_program_order (a b tiles) {left right} (he : Tma.ProgramOrder (dataCompleteCandidate a b tiles).view left right) :
    controlRank tiles left < controlRank tiles right := by
  cases left <;> cases right <;> try exact False.elim he
  exact source_control_strict tiles _ _ he.2.2.1 he.2.2.2

theorem control_internal_order (a b tiles) {left right} (he : Tma.InternalEdge (dataCompleteCandidate a b tiles).view left right) :
    controlRank tiles left < controlRank tiles right := by
  cases he <;> dsimp only [controlRank] <;> omega

theorem producer_tick_before (tiles serial) (hs : serial < producerThreshold tiles) : producerTick tiles serial = serial := by
  simp only [producerTick,ite_eq_right (by omega : ¬producerThreshold tiles ≤ serial),Nat.add_zero]
theorem producer_tick_after (tiles serial) (hs : producerThreshold tiles ≤ serial) : producerTick tiles serial = serial+3 := by
  simp only [producerTick,ite_eq_left hs]

theorem peer_wait_tick (tiles tile) (ht : tile < tiles) : peerTick tiles (2+7*tile) = 8+10*tile := by
  simp only [peerTick]
  split_ifs <;> omega

theorem peer_native_tick (tiles tile offset) (ht : tile < tiles) (ho : 1 ≤ offset ∧ offset ≤ 6) :
    peerTick tiles (2+7*tile+offset) = 8+10*tile+offset+3 := by
  simp only [peerTick]
  split_ifs <;> omega

theorem peer_tail_tick (tiles offset) : peerTick tiles (2+7*tiles+offset) = 8+10*tiles+offset := by
  simp only [peerTick]
  split_ifs <;> omega

theorem producer_wait_tick (tiles tile) (ht : tile < tiles) : producerTick tiles (8+10*tile) = 8+10*tile := by
  apply producer_tick_before
  simp only [producerThreshold]
  split_ifs <;> omega

theorem producer_initial_tick (tiles) (serial : Nat) (hs : serial ≤ 4) : producerTick tiles serial = serial := by
  apply producer_tick_before
  simp only [producerThreshold]
  split_ifs <;> omega

theorem producer_tail_tick (tiles offset) : producerTick tiles (10*tiles+5+offset) = 8+10*tiles+offset := by
  have hs : producerThreshold tiles ≤ 10*tiles+5+offset := by simp only [producerThreshold]; split_ifs <;> omega
  rw [producer_tick_after tiles _ hs]
  omega

end
end Ptx.Kernels.HopperDoubleBuffer
