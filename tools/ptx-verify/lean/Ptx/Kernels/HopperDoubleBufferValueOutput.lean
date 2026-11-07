import Ptx.Kernels.HopperDoubleBufferValueExecution
import Ptx.Iris.ByteContentsWrites

/-! Actual final native heap cells contain the existing real-valued GEMM
specification fragments. This is value-state/source correspondence, not IEEE
storage or a physical GPU/runtime allocation result.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
open Iris.ProgramLogic
noncomputable section

theorem retry_data_value_output_of_unique_writes {a b tiles schedules next}
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hi : ByteContentsHeap.UniqueWrites (byteContentsContext (retryDataFamily a b tiles schedules)) next)
    (hcut : next.coupled.done = Present (retryDataCandidate a b tiles schedules))
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt next ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      some (.realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val) := by
  let family := retryDataFamily a b tiles schedules
  have hsource := retry_data_source a b tiles schedules (fun _ => .bits (byte 0)) ht hb
  have hcomplete := retry_data_complete a b tiles schedules ht hb
  have hwrite := retry_actual_output_byte family hsource lane slot index
  change ByteContents.writeByte (retryDataCandidate a b tiles schedules) (.base (.tma (.source (family.storeId lane slot))))
    ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
    some (.realPart .f32 ((replyCheckpoint tiles lane (retryDataOracle a b tiles schedules lane) (schedules lane)).2 slot) index.val) at hwrite
  rw [retry_data_final_accumulation] at hwrite
  apply hi _ _ _ hwrite
  · intro other written hw
    exact retry_global_unique_writers family hb hsource hcomplete rfl hw hwrite
  · rw [hcut]
    exact kernel_use_present (ordinary_write_use hwrite)

theorem retry_data_value_output_of_run {a b tiles schedules frame protocol actions next}
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hr : IrisExecution.run (ByteContentsHeap.transition (byteContentsContext (retryDataFamily a b tiles schedules))) actions
      (retryValueInitialState a b tiles schedules frame protocol) = .ok next)
    (hcut : next.coupled.done = Present (retryDataCandidate a b tiles schedules))
    (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4) :
    ByteContents.valueAt next ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
      some (.realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val) := by
  apply retry_data_value_output_of_unique_writes ht hb _ hcut lane slot index
  exact ByteContentsHeap.unique_writes_run (byteContentsContext (retryDataFamily a b tiles schedules)) actions
    (ByteContentsHeap.unique_writes_initial (by intro node h; exact h)) hr

theorem retry_data_value_matrix_witness (a b tiles schedules frame protocol) (ht : 0 < tiles) (hb : tiles ≤ 2^28) :
    ∃ actions next,
      IrisExecution.run (ByteContentsHeap.transition (byteContentsContext (retryDataFamily a b tiles schedules))) actions
        (retryValueInitialState a b tiles schedules frame protocol) = .ok next ∧
      next.coupled.done = Present (retryDataCandidate a b tiles schedules) ∧
      next.coupled.protocol = protocol ∧ ByteContentsHeap.Available next ∧
      (∀ (lane : Wgmma.Lane) (slot : Wgmma.Slot) (index : Fin 4), ByteContents.valueAt next ((⟨.global,outputWordAddress (lane,slot)⟩ : Location).add index.val) =
        some (.realPart .f32 (specification a b tiles (Wgmma.cCoord (lane,slot))) index.val)) ∧
      adequate .NotStuck (ByteContentsHeap.script (byteContentsContext (retryDataFamily a b tiles schedules)) actions)
        (retryValueInitialState a b tiles schedules frame protocol) (fun result _ => result = .ok next) := by
  obtain ⟨actions,next,hr,hcut,hprotocol,ha,hadequate⟩ := retry_data_value_native_witness a b tiles schedules frame protocol ht hb
  exact ⟨actions,next,hr,hcut,hprotocol,ha,retry_data_value_output_of_run ht hb hr hcut,hadequate⟩

end
end Ptx.Kernels.HopperDoubleBuffer
