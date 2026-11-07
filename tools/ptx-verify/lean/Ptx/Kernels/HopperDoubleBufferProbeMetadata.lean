import Ptx.Kernels.HopperDoubleBufferSourceProbes
import Ptx.Kernels.HopperDoubleBufferPhases

/-! Finite projections of the actual T=3 source probes: prefetch, two arenas,
reuse parity and group acknowledgment. Equality is over metadata only. These
facts are not full candidate memory or protocol-history admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def transferMetadata : Wgmma.Event → Option (Nat × Nat × Int × Nat)
  | .base (.tmaIssue op) => some (op.destination,op.descriptorAddress,op.coordinates.y,op.barrier)
  | _ => none
def waitMetadata : Wgmma.Event → Option (Nat × Nat × Bool)
  | .base (.barrier e) => match e.operation with | .tryWaitParity parity ready => some (e.location.address,parity,ready) | _ => none
  | _ => none
def matrixMetadata : Wgmma.Event → Option (Nat × Nat × Nat)
  | .mma _ call => some (call.group,call.a,call.b)
  | _ => none
def completeMetadata : Wgmma.Event → Option (Nat × Nat × Nat)
  | .wait _ _ keep before after _ => some (before,after,keep)
  | _ => none
def orderingMetadata : Wgmma.Event → Option Nat
  | .base (.tmaIssue op) => some (if op.descriptorAddress = 4096 then 10+op.destination else 20+op.destination)
  | .mma _ call => some (10000+call.group)
  | .wait _ _ _ _ after _ => some (20000+after)
  | _ => none

theorem producer_three_tile_transfers : (probeTrace 3 0).events.filterMap transferMetadata = [
    (16,4096,0,0),(2064,4224,0,0),(2320,4096,8,8),(4368,4224,1,8),(16,4096,16,0),(2064,4224,2,0)] := by decide
theorem producer_three_tile_waits : (probeTrace 3 0).events.filterMap waitMetadata = [(0,0,true),(8,0,true),(0,1,true)] := by decide
theorem peer_three_tile_waits : (probeTrace 3 1).events.filterMap waitMetadata = [(0,0,true),(8,0,true),(0,1,true)] := by decide
theorem three_tile_descriptors : ∀ who : Fin 2, (probeTrace 3 who).events.filterMap matrixMetadata =
    [(0,68720001025,68720001153),(1,68720001169,68720001297),(2,68720001025,68720001153)] := by decide
theorem three_tile_completion : ∀ who : Fin 2, (probeTrace 3 who).events.filterMap completeMetadata = [(0,1,0),(1,2,0),(2,3,0)] := by decide
theorem producer_prefetch_and_reuse_order : (probeTrace 3 0).events.filterMap orderingMetadata =
    [26,2084,2330,4388,10000,20001,26,2084,10001,20002,10002,20003] := by decide
theorem zero_tile_has_no_transfer : (probeTrace 0 0).events.filterMap transferMetadata = [] := by decide
theorem zero_tile_has_no_native_call : ∀ who : Fin 2, (probeTrace 0 who).events.filterMap matrixMetadata = [] := by decide
theorem producer_both_stages_reused : (probeTrace 4 0).events.filterMap waitMetadata = [(0,0,true),(8,0,true),(0,1,true),(8,1,true)] := by decide
theorem producer_parity_wraps : (probeTrace 5 0).events.filterMap waitMetadata = [(0,0,true),(8,0,true),(0,1,true),(8,1,true),(0,0,true)] := by decide
theorem first_reuse_has_changed_parity : expectedParity 0 = 0 ∧ expectedParity 2 = 1 ∧ stage 0 = stage 2 := by decide

end
end Ptx.Kernels.HopperDoubleBuffer
