import Ptx.Kernels.ShuffleProbeLaunch
import Ptx.ISA.ThreadEnumeration

/-! Construct complete collective source candidates from finite launch
identities and actual generated-code runs. Agreement is proved for the chosen
oracles. This joins source/control/definedness/agreement, not yet the ordinary
memory/observer witness required by Shuffle.Nonvacuous. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

def witnessOracle (mode : Mode) (input : Inputs) (launch : Scalar.Launch) (id : ThreadId) : Shuffle.Oracle :=
  ⟨fun _ => .integer 0,fun _ => (expectedWord mode input (context launch id),expectedPredicate mode input (context launch id))⟩
def witnessTrace (mode : Mode) (input : Inputs) (launch : Scalar.Launch) (id : ThreadId) : Shuffle.ThreadTrace :=
  ⟨id,witnessOracle mode input launch id,24,
    finalState mode input (context launch id) (expectedWord mode input (context launch id)) (expectedPredicate mode input (context launch id)),
    events mode input (context launch id) (expectedWord mode input (context launch id)) (expectedPredicate mode input (context launch id))⟩
def witnessCandidate (mode : Mode) (input : Inputs) (launch : Scalar.Launch) : Shuffle.Candidate :=
  ⟨launch.geometry.threadIds.map (witnessTrace mode input launch)⟩

theorem witness_trace_produced (mode : Mode) (input : Inputs) (launch : Scalar.Launch) (id : ThreadId)
    (hp : Params input launch.params) :
    Produced (code mode) launch.params launch.geometry.block (witnessTrace mode input launch id) :=
  complete_source_run mode input (context launch id) (witnessOracle mode input launch id) hp

theorem witness_well_formed (mode : Mode) (input : Inputs) (launch : Scalar.Launch)
    (hg : launch.geometry.Valid) (hp : Params input launch.params) :
    Shuffle.WellFormed (code mode) launch (witnessCandidate mode input launch) := by
  refine ⟨hg,?_,?_,?_⟩
  · simpa only [witnessCandidate,List.map_map,Function.comp_def,witnessTrace,List.map_id'] using launch.geometry.threadIds_nodup
  · intro trace ht
    obtain ⟨id,hi,rfl⟩ := List.mem_map.mp ht
    exact ⟨Geometry.threadIds_valid hg hi,witness_trace_produced mode input launch id hp⟩
  · intro id hv
    exact ⟨witnessTrace mode input launch id,List.mem_map.mpr ⟨id,Geometry.threadIds_cover hg hv,rfl⟩,rfl⟩

theorem witness_complete (mode : Mode) (input : Inputs) (launch : Scalar.Launch) :
    Shuffle.Complete (witnessCandidate mode input launch) := by
  intro trace ht
  obtain ⟨id,_,rfl⟩ := List.mem_map.mp ht
  rfl

theorem witness_reply_values {mode input launch trace}
    (ht : trace ∈ (witnessCandidate mode input launch).traces) :
    w32 (trace.oracle.shuffle 0).1 = expectedWord mode input (context launch trace.id) ∧
    (trace.oracle.shuffle 0).2 = expectedPredicate mode input (context launch trace.id) := by
  obtain ⟨id,_,rfl⟩ := List.mem_map.mp ht
  exact ⟨w32_idem _,rfl⟩

theorem witness_agreement (mode : Mode) (input : Inputs) (launch : Scalar.Launch)
    (hg : launch.geometry.Valid) (hp : Params input launch.params) :
    Agreement launch.geometry.block (witnessCandidate mode input launch) := by
  have hw := witness_well_formed mode input launch hg hp
  have hc := witness_complete mode input launch
  intro origin result he _ peerEvent peerRecord hpeer hsource
  obtain ⟨trace,ht,hi,_,hr⟩ := actual_shuffle_shape hp hw hc he
  obtain ⟨peer,hm,hid,_,hrecord⟩ := actual_shuffle_shape hp hw hc hpeer
  rw [hr,hrecord] at hsource ⊢
  have hs : SameWarp launch.geometry.block trace.id peer.id := by simpa only [hi,hid] using hsource.1
  have hl : lane launch.geometry.block peer.id =
      (select mode (lane launch.geometry.block trace.id) (w32 input.b) (w32 input.c)).source := by
    simpa only [hi,hid,record,groupKey] using hsource.2.1
  have hv : inputWord input (context launch peer.id) = expectedWord mode input (context launch trace.id) := by
    simpa only [context] using (selected_peer_input_is_spec (mode := mode) (input := input)
      (ctx := context launch trace.id) (peer := peer.id) hs hl)
  obtain ⟨hvalue,hpredicate⟩ := witness_reply_values ht
  constructor
  · exact hvalue.trans hv.symm
  · simpa only [record,groupKey,expectedPredicate,context,hi] using hpredicate

theorem complete_collective_source_witness (mode : Mode) (input : Inputs) (launch : Scalar.Launch)
    (hp : SafePre mode input launch) :
    ∃ candidate, Shuffle.WellFormed (code mode) launch candidate ∧ Shuffle.Complete candidate ∧
      ControlAdmitted launch.geometry.block candidate ∧ Defined launch.geometry.block candidate ∧
      Agreement launch.geometry.block candidate := by
  have hw := witness_well_formed mode input launch hp.1 hp.2.1
  have hc := witness_complete mode input launch
  exact ⟨witnessCandidate mode input launch,hw,hc,all_completed_control_admitted hp.2.1 hw hc,
    all_completed_defined hp.2.1 hp.2.2 hw hc,witness_agreement mode input launch hp.1 hp.2.1⟩

end
end Ptx.Kernels.ShuffleProbe
