import Ptx.Kernels.HopperDoubleBufferLoopSchedule
import Ptx.Kernels.HopperDoubleBufferLoopWitness

/-! Source-native query inversion for the successful-wait witness. Producer
queries include prefetches except on the final tile; consumers never prefetch.
This arithmetic identifies reply origins, not resource or memory admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper

def initialQuery (leader : Bool) : Nat := if leader then 4 else 0
def nativeQuery (tiles tile : Nat) (leader : Bool) : Nat :=
  if leader then (if tile+1 < tiles then 9+7*tile else 5+7*tile) else 1+3*tile

def nativeTile (tiles : Nat) (leader : Bool) (query : Nat) : Nat :=
  if leader then (if query = 5+7*(tiles-1) then tiles-1 else (query-9)/7) else (query-1)/3

def aPayloadTile (query : Nat) : Nat := if query = 1 then 0 else 1+(query-6)/7

def bPayloadTile (query : Nat) : Nat := if query = 3 then 0 else 1+(query-8)/7

theorem zero_retry_sum (first n : Nat) : loopRetryCount first zeroRetries n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [loopRetryCount,zeroRetries,ih]

theorem loop_query_before_tile (tiles tile : Nat) (leader : Bool) (ht : tile < tiles) :
    loopQuery 0 tiles leader zeroRetries (initialQuery leader) tile = if leader then 4+7*tile else 3*tile := by
  rw [loopQuery_accounting,zero_retry_sum]
  cases leader
  · simp [initialQuery,loopPrefetchCount_consumer]
  · rw [loopPrefetchCount_prefix 0 tiles tile (by omega) (by omega)]
    simp only [initialQuery,ite_true]
    have hmin : min tile (tiles-0-1) = tile := by omega
    rw [hmin]
    omega

theorem native_query_at_tile (tiles tile : Nat) (leader : Bool) (ht : tile < tiles) :
    loopQuery 0 tiles leader zeroRetries (initialQuery leader) tile+1+
      (if needsPrefetch tile tiles leader then 4 else 0) = nativeQuery tiles tile leader := by
  rw [loop_query_before_tile tiles tile leader ht]
  cases leader <;> by_cases hn : tile+1 < tiles <;> simp [nativeQuery,needsPrefetch,hn] <;> omega

theorem native_tile_inverse (tiles tile : Nat) (leader : Bool) (ht : tile < tiles) :
    nativeTile tiles leader (nativeQuery tiles tile leader) = tile := by
  cases leader <;> by_cases hn : tile+1 < tiles
  all_goals simp only [nativeTile,nativeQuery,hn,ite_true,ite_false]
  all_goals split_ifs <;> omega

theorem native_queries_unique (tiles : Nat) (leader : Bool) {left right : Nat}
    (hl : left < tiles) (hr : right < tiles) (he : nativeQuery tiles left leader = nativeQuery tiles right leader) : left = right := by
  have h := congrArg (nativeTile tiles leader) he
  simpa only [native_tile_inverse tiles left leader hl,native_tile_inverse tiles right leader hr] using h

theorem initial_payload_tiles : aPayloadTile 1 = 0 ∧ bPayloadTile 3 = 0 := ⟨rfl,rfl⟩
theorem prefetch_payload_tiles (tile : Nat) : aPayloadTile (6+7*tile) = tile+1 ∧ bPayloadTile (8+7*tile) = tile+1 := by
  have ha : 6+7*tile ≠ 1 := by omega
  have hb : 8+7*tile ≠ 3 := by omega
  simp [aPayloadTile,bPayloadTile,ha,hb,Nat.add_comm]

end Ptx.Kernels.HopperDoubleBuffer
