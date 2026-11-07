import Ptx.Kernels.HopperDoubleBufferAsyncCoverage
import Ptx.Kernels.HopperDoubleBufferProgress
import Ptx.Kernels.HopperDoubleBufferRetryArbitraryObservations
import Ptx.Hopper.ProtocolScript

/-! All tickets in the aggregate prepared plan name actual own-phase TMA or
native work. Source-matched complete prefixes discharge every completion guard.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

theorem async_plan_full_completed {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (htma : Unified.TmaComponents code (completeLaunch tiles initial) candidate Tma.localShared (dataMaps tiles) (retryHistories family)) :
    Bridge.AllCompleted Tma.localShared candidate (retryHistories family) dataCluster (asyncPlan family) (Present candidate) := by
  intro ticket work hm
  obtain ⟨tile,hp,ha | hb' | hn⟩ := async_plan_work family hm
  · subst work
    have hc := family_copy_a_at family htma.source tile hp
    refine .tma hc ?_ (arbitrary_histories_completion_observations family ht htma
      (retry_control_admitted family ht hb htma.source) tile hp 0).1 ?_
    · rw [family_copy_a_descriptor family htma.source htma.descriptors tile hp]
      norm_num [aView,Tma.Descriptor2D.bytes]
    · simp only [Present,Tma.Present,Hopper.Candidate.Present,Unified.view_eventAt,
        family_wait_at family htma.source tile hp 0,Option.map_some,Option.isSome_some]
  · subst work
    have hc := family_copy_b_at family htma.source tile hp
    refine .tma hc ?_ (arbitrary_histories_completion_observations family ht htma
      (retry_control_admitted family ht hb htma.source) tile hp 0).2 ?_
    · rw [family_copy_b_descriptor family htma.source htma.descriptors tile hp]
      norm_num [bView,Tma.Descriptor2D.bytes]
    · simp only [Present,Tma.Present,Hopper.Candidate.Present,Unified.view_eventAt,
        family_wait_at family htma.source tile hp 0,Option.map_some,Option.isSome_some]
  · subst work
    refine .native (retry_native_completed family htma.source hb tile hp 0) ?_
    simp only [Present,Tma.Present,Hopper.Candidate.Present,Unified.view_eventAt,
      family_native_wait_at family htma.source hb tile hp 0,Option.map_some,Option.isSome_some]

end
end Ptx.Kernels.HopperDoubleBuffer
