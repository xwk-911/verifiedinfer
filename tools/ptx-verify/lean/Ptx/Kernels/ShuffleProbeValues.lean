import Ptx.Kernels.ShuffleProbeSource
import Ptx.Kernels.ShuffleProbeIndex

/-! Every actual store carries the independent integer word/predicate spec.
This consumes checked collective definedness and agreement; observed output
arrays still require writer uniqueness, observation and non-vacuity proofs. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

theorem agreed_stores_have_independent_values {mode : Mode} {input : Inputs} {launch : Scalar.Launch}
    {candidate : Shuffle.Candidate} {trace : Shuffle.ThreadTrace}
    (hp : Params input launch.params) (hw : Shuffle.WellFormed (code mode) launch candidate)
    (hc : Shuffle.Complete candidate) (hd : Defined launch.geometry.block candidate)
    (ha : Agreement launch.geometry.block candidate) (ht : trace ∈ candidate.traces) :
    candidate.view.eventAt ⟨trace.id,0⟩ = some (.write (outputLoc input (context launch trace.id) 0)
      ((encodeU32 (expectedWord mode input (context launch trace.id))).map Symbolic.Byte.bits)) ∧
    candidate.view.eventAt ⟨trace.id,1⟩ = some (.write (outputLoc input (context launch trace.id) 4)
      ((encodeU32 (if expectedPredicate mode input (context launch trace.id) then 1 else 0)).map Symbolic.Byte.bits)) := by
  obtain ⟨peer,_,hs,hl,hvalue,hpredicate⟩ := agreed_value_is_actually_stored hp hw hc hd ha ht
  have hv : inputWord input (context launch peer.id) = expectedWord mode input (context launch trace.id) := by
    simpa only [context] using (selected_peer_input_is_spec (mode := mode) (input := input)
      (ctx := context launch trace.id) (peer := peer.id) hs hl)
  constructor
  · simpa only [hv] using hvalue
  · exact hpredicate

end
end Ptx.Kernels.ShuffleProbe
