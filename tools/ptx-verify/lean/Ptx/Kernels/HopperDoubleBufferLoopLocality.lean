import Ptx.Kernels.HopperDoubleBufferLoop

/-! Loop prefixes depend only on their executed retry entries. Future schedule
updates preserve full states, arithmetic fragments, query IDs, fuel and events.
These are equalities of the original definitions, not an alternate executor. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section

theorem loop_query_retry_congr {first tiles leader left right query n}
    (he : ∀ i < n, left (first+i) = right (first+i)) :
    loopQuery first tiles leader left query n = loopQuery first tiles leader right query n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [loopQuery,loopQuery,ih (fun i hi => he i (by omega)),he n (by omega)]

theorem loop_fuel_retry_congr {first tiles leader left right n}
    (he : ∀ i < n, left (first+i) = right (first+i)) :
    loopFuel first tiles leader left n = loopFuel first tiles leader right n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [loopFuel,loopFuel,ih (fun i hi => he i (by omega)),he n (by omega)]

theorem loop_checkpoint_retry_congr {ctx oracle first tiles leader left right s values n}
    (he : ∀ i < n, left (first+i) = right (first+i)) :
    loopCheckpoint ctx oracle first tiles leader left s values n = loopCheckpoint ctx oracle first tiles leader right s values n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [loopCheckpoint,loopCheckpoint,ih (fun i hi => he i (by omega)),he n (by omega)]

theorem loop_events_retry_congr {ctx oracle first tiles leader left right s values mapA mapB n}
    (he : ∀ i < n, left (first+i) = right (first+i)) :
    loopEvents ctx oracle first tiles leader left s values mapA mapB n =
      loopEvents ctx oracle first tiles leader right s values mapA mapB n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [loopEvents,loopEvents,ih (fun i hi => he i (by omega)),
      loop_checkpoint_retry_congr (fun i hi => he i (by omega)),he n (by omega)]

end
end Ptx.Kernels.HopperDoubleBuffer
