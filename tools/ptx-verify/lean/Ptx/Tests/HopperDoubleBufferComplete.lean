import Ptx.Kernels.HopperDoubleBufferWriteInventory

/-! Actual complete-source runs and ordinary output byte metadata. Source
completion is not graph admission, and symbolic real bytes are not an IEEE/GPU
result. All evaluated equalities exclude real-valued state equality. -/
namespace Ptx.HopperDoubleBufferCompleteTests
open Ptx.ISA Ptx.Hopper Ptx.Kernels.HopperDoubleBuffer
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def source (tiles : Nat) (lane : Wgmma.Lane) :=
  (Wgmma.run (ctx tiles lane) (oracle tiles) code (completeSteps tiles lane) {}).toOption
structure Metadata where
  pc : Nat
  query : Nat
  groups : Nat
  completed : Nat
  pending : Nat
  calls : Nat
  done : Bool
  deriving DecidableEq

def metadata (tiles : Nat) (lane : Wgmma.Lane) : Option Metadata :=
  (source tiles lane).map fun r => ⟨r.1.base.scalar.core.thread.pc,r.1.base.scalar.core.queries,r.1.ledger.groups,
    r.1.ledger.completed,(Wgmma.pending r.1.ledger).length,r.1.ledger.calls.length,r.1.base.scalar.core.thread.status == .done⟩
def writes (tiles : Nat) (lane : Wgmma.Lane) :=
  (source tiles lane).map fun r => (r.2.filterMap globalWrite).map (fun item => (item.1,item.2.length))
def invalidationMetadata : Wgmma.Event → Option Nat
  | .base (.barrier e) => match e.operation with | .inval => some e.location.address | _ => none
  | _ => none
def invalidated (tiles : Nat) (lane : Wgmma.Lane) := (source tiles lane).map fun r => r.2.filterMap invalidationMetadata

def byteTag : Symbolic.Byte → Nat × Nat
  | .realPart format _ index => (format.bytes,index)
  | .bits _ => (0,0)
  | .tensorMapPart _ index => (128,index)
def byteTags (tiles : Nat) (lane : Wgmma.Lane) :=
  (source tiles lane).map fun r => (r.2.filterMap globalWrite).map (fun item => item.2.map byteTag)
def typedF32Bytes : List (Nat × Nat) := [(4,0),(4,1),(4,2),(4,3)]

theorem six_tiles_producer_returns : metadata 6 0 = some ⟨100,42,6,6,0,6,true⟩ := by decide
theorem six_tiles_peer_returns : metadata 6 127 = some ⟨100,18,6,6,0,6,true⟩ := by decide
theorem six_tiles_interior_returns : metadata 6 43 = some ⟨100,18,6,6,0,6,true⟩ := by decide
theorem zero_tiles_producer_returns : metadata 0 0 = some ⟨100,0,0,0,0,0,true⟩ := by decide
theorem zero_tiles_peer_returns : metadata 0 127 = some ⟨100,0,0,0,0,0,true⟩ := by decide
theorem producer_store_addresses : writes 6 0 = some [(8192,4),(8196,4),(8448,4),(8452,4)] := by decide
theorem last_lane_store_addresses : writes 6 127 = some [(9976,4),(9980,4),(10232,4),(10236,4)] := by decide
theorem interior_lane_store_addresses : writes 6 43 = some [(8792,4),(8796,4),(9048,4),(9052,4)] := by decide
theorem zero_tiles_still_write_all_outputs : writes 0 127 = some [(9976,4),(9980,4),(10232,4),(10236,4)] := by decide
theorem producer_invalidates_both_barriers : invalidated 6 0 = some [0,8] := by decide
theorem peer_does_not_invalidate_barriers : invalidated 6 127 = some [] := by decide
theorem zero_tiles_invalidates_both_barriers : invalidated 0 0 = some [0,8] := by decide
theorem stores_retain_typed_byte_indices : byteTags 6 127 = some [typedF32Bytes,typedF32Bytes,typedF32Bytes,typedF32Bytes] := by decide
theorem producer_full_fuel : completeSteps 6 0 = 259 := by decide
theorem peer_full_fuel : completeSteps 6 127 = 203 := by decide
theorem zero_producer_full_fuel : completeSteps 0 0 = 51 := by decide
theorem zero_peer_full_fuel : completeSteps 0 127 = 46 := by decide

theorem first_output_byte : outputByteAddress (0,0) 0 = 8192 := by decide
theorem last_output_byte : outputByteAddress (127,3) 3 = 10239 := by decide

end
end Ptx.HopperDoubleBufferCompleteTests
