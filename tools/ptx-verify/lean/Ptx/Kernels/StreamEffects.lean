import Ptx.Kernels.ScalarSourceChecked
import Ptx.Event.Publication

/-! Publication-domain coverage derived from actual source writes. These are
effect theorems, not additional assumptions about callers' input memory. -/
namespace Ptx.ScalarMatmulEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarMatmul
noncomputable section

theorem covers_global_writes {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {domain : List Location} (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) (hc : CoversOutput cfg domain) :
    CoversGlobalWrites execution domain := by
  intro writer loc value _ hwrite
  obtain ⟨_,ha,_,answer,hpayload⟩ := write_shape hw hd hg hp hwrite
  obtain ⟨offset,hb,rfl⟩ := payload_location hpayload
  exact hc _ _ ha.1 ha.2 offset (by simpa only [Symbolic.encode_length,Symbolic.Format.bytes] using hb)

end
end Ptx.ScalarMatmulEvent

namespace Ptx.ScalarAttentionEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarAttention
noncomputable section

theorem covers_global_writes {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    {domain : List Location} (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) (hc : CoversOutput cfg domain) :
    CoversGlobalWrites execution domain := by
  intro writer loc value _ hwrite
  obtain ⟨_,ha,_,answer,hpayload⟩ := write_shape hw hd hg hp hwrite
  obtain ⟨offset,hb,rfl⟩ := payload_location hpayload
  exact hc _ _ ha.1 ha.2 offset (by simpa only [Symbolic.encode_length,Symbolic.Format.bytes] using hb)

end
end Ptx.ScalarAttentionEvent

namespace Ptx.FloatLiteralsUniversal
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.FloatLiteralsMemory
noncomputable section

theorem covers_global_writes {dst : Nat} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hp : Pre dst launch) (hw : Scalar.WellFormed FloatLiteralsTrace.code launch execution) (hd : execution.Complete) :
    CoversGlobalWrites execution (domain dst) := by
  obtain ⟨answer,he⟩ := candidate_view hp hw hd
  intro writer loc value hg hwrite
  rw [SameEvents.writes he] at hwrite
  rcases FloatLiteralsMemory.write_shape hwrite with ⟨_,hpayload⟩ | ⟨_,hpayload⟩
  · have hb := (payloadByte_bounds hpayload).1
    simp [hg,sharedLoc] at hb
  · obtain ⟨offset,hb,rfl⟩ := payload_location hpayload
    apply List.mem_map.mpr
    exact ⟨offset,List.mem_range.mpr (by simpa only [Symbolic.encode_length,Symbolic.Format.bytes] using hb),rfl⟩

end
end Ptx.FloatLiteralsUniversal
