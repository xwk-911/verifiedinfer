import Ptx.Kernels.HopperDoubleBufferLoopWitness
import Ptx.Kernels.HopperStageCheckpoints

/-! The real kernel prologue through PC 28, including runtime descriptor
construction. The producer predicate is derived from the launch coordinates;
subsequent barrier/TMA initialization and output are separate source segments.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def entryRegs (tiles : Nat) (lane : Wgmma.Lane) (flag : Nat) : Bindings := [
  ("%bd1",wrap 64 68720001297),("%ad1",wrap 64 68720001169),
  ("%bd0",wrap 64 68720001153),("%ad0",wrap 64 68720001025),
  ("%bar1",8),("%bar0",0),("%leader",flag),("%sum",HopperStage.sumWord lane),
  ("%z",HopperStage.zWord lane),("%y",HopperStage.yWord lane),("%x",HopperStage.xWord lane),
  ("%tiles",wrap 32 tiles),("%out",wrap 64 8192),("%mapb",wrap 64 4224),("%mapa",wrap 64 4096)]
def entryDirtyAt (n : Nat) : List String := (List.range n).foldl (fun names pc =>
  (((code[pc]?).map Wgmma.ordinaryNames).getD []++names).eraseDups) []
def entryState (tiles : Nat) (lane : Wgmma.Lane) (flag : Nat) : Wgmma.State := {
  base := {scalar := {core := {thread := {pc := 28,regs := entryRegs tiles lane flag}},floats := HopperStage.zeroFloats}}
  ledger := {dirty := entryDirtyAt 28}
}

def entryPartial (pc skip tiles : Nat) (lane : Wgmma.Lane) (flag : Nat) : Wgmma.State := {
  base := {scalar := {core := {thread := {pc := pc,regs := (entryRegs tiles lane flag).drop skip}}}}
  ledger := {dirty := entryDirtyAt pc}
}

theorem entry_first_twelve (tiles : Nat) (lane : Wgmma.Lane) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code 12 {} =
      .ok (entryPartial 12 4 tiles lane (HopperStage.leaderWord lane),[]) := by rfl

theorem entry_descriptor_a0 (tiles : Nat) (lane : Wgmma.Lane) (flag : Nat) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code 3 (entryPartial 12 4 tiles lane flag) =
      .ok (entryPartial 15 3 tiles lane flag,[]) := by rfl

theorem entry_descriptor_b0 (tiles : Nat) (lane : Wgmma.Lane) (flag : Nat) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code 3 (entryPartial 15 3 tiles lane flag) =
      .ok (entryPartial 18 2 tiles lane flag,[]) := by rfl

theorem entry_descriptor_a1 (tiles : Nat) (lane : Wgmma.Lane) (flag : Nat) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code 3 (entryPartial 18 2 tiles lane flag) =
      .ok (entryPartial 21 1 tiles lane flag,[]) := by rfl

theorem entry_descriptor_b1 (tiles : Nat) (lane : Wgmma.Lane) (flag : Nat) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code 3 (entryPartial 21 1 tiles lane flag) =
      .ok (entryPartial 24 0 tiles lane flag,[]) := by rfl

theorem entry_zero_accumulators (tiles : Nat) (lane : Wgmma.Lane) (flag : Nat) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code 4 (entryPartial 24 0 tiles lane flag) =
      .ok (entryState tiles lane flag,[]) := by rfl

theorem entry_prefix (tiles : Nat) (lane : Wgmma.Lane) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code 28 {} = .ok (entryState tiles lane (HopperStage.leaderWord lane),[]) := by
  rw [show 28 = 12+3+3+3+3+4 from rfl,Wgmma.run_add,Wgmma.run_add,Wgmma.run_add,Wgmma.run_add,Wgmma.run_add,entry_first_twelve]
  simp only [Except.bind,entry_descriptor_a0,entry_descriptor_b0,entry_descriptor_a1,entry_descriptor_b1,
    entry_zero_accumulators,List.nil_append]

theorem entry_producer_flag (tiles : Nat) (lane : Wgmma.Lane) :
    Wgmma.run (ctx tiles lane) (oracle tiles) code 28 {} =
      .ok (entryState tiles lane (if HopperStage.leader lane then 1 else 0),[]) := by
  rw [entry_prefix,HopperStage.leader_word_value]

theorem entry_tile_count (tiles : Nat) (lane : Wgmma.Lane) (flag : Nat) (hb : tiles ≤ 2^28) :
    lookup "%tiles" (entryState tiles lane flag).base.scalar.core.thread.regs = some tiles := by
  have hw : wrap 32 tiles = tiles := Nat.mod_eq_of_lt (by omega)
  simp [entryState,entryRegs,lookup,hw]

theorem entry_unique_producer (lane : Wgmma.Lane) : HopperStage.leader lane = true ↔ lane.val = 0 := by
  simp [HopperStage.leader]

end
end Ptx.Kernels.HopperDoubleBuffer
