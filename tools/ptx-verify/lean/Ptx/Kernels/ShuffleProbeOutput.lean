import Ptx.Kernels.ShuffleProbeMemoryWitness
import Ptx.Kernels.ShuffleProbeValues
import Ptx.Scalar.IntegerMemory

/-! Final output arrays for all completed admitted executions of the exported
shuffle probes. The specification uses mathematical launch indices, not oracle
replies or final registers. Complete witnesses and source safety are separate
obligations and are joined below. Physical allocation/runtime remain external. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

def ArrayCovered (input : Inputs) (launch : Scalar.Launch) (domain : List Location) : Prop :=
  ∀ id, id.Valid launch.geometry → ∀ offset, offset < 8 →
    (⟨.global,input.out+8*linear launch.geometry.block id+offset⟩ : Location) ∈ domain

def ArrayValues (mode : Mode) (input : Inputs) (launch : Scalar.Launch) (output : Scalar.ByteMap) : Prop :=
  ∀ id, id.Valid launch.geometry →
    Scalar.RepresentsU32 output ⟨.global,input.out+8*linear launch.geometry.block id⟩
      (expectedWord mode input (context launch id)) ∧
    Scalar.RepresentsU32 output ⟨.global,input.out+8*linear launch.geometry.block id+4⟩
      (if expectedPredicate mode input (context launch id) then 1 else 0)

def ArrayFootprint (input : Inputs) (launch : Scalar.Launch) (loc : Location) : Prop :=
  loc.space = .global ∧ input.out ≤ loc.address ∧ loc.address < input.out+8*launch.geometry.block.volume

theorem output_footprint_in_array {input launch loc} (hg : launch.geometry.Valid)
    (hl : LayoutPre input launch) (hf : OutputFootprint input launch loc) : ArrayFootprint input launch loc := by
  obtain ⟨id,hi,slot,hslot,hspace,hlo,hhi⟩ := hf
  have hs : slot ≤ 4 := by rcases hslot with rfl | rfl <;> decide
  have hloc := output_location_layout hg hl hi hs
  rw [hloc] at hlo hhi
  have hn := Dim3.linear_lt_volume hg.2 hi.2
  change linear launch.geometry.block id < launch.geometry.block.volume at hn
  exact ⟨hspace,by simp only at hlo; omega,by simp only at hhi; omega⟩

def ArrayPost (mode : Mode) (input : Inputs) (domain : Scalar.Launch → List Location)
    (launch : Scalar.Launch) (output : Scalar.ByteMap) : Prop :=
  ArrayValues mode input launch output ∧
    ∀ loc ∈ domain launch, ¬ArrayFootprint input launch loc → output loc = launch.initial loc

theorem observe_unique_output_word {mode input launch candidate rf co observation writer base value}
    (hp : Params input launch.params) (hw : Shuffle.WellFormed (code mode) launch candidate)
    (hc : Shuffle.Complete candidate) (hl : LayoutPre input launch)
    (hm : Ptx.Event.GenericMemoryConditions candidate.view launch.initial rf co)
    (ho : Ptx.Event.ObserverConditions candidate.view launch.initial rf co observation)
    (he : candidate.view.eventAt writer = some (.write base (Scalar.u32Bytes value)))
    (hd : ∀ offset, offset < 4 → base.add offset ∈ observation.domain) :
    Scalar.RepresentsU32 observation.output base value := by
  apply Scalar.observe_u32_write hm ho he hd
  · intro offset _
    exact Ptx.Event.unique_byte_observer_eligible (no_mixed_size_races hp hw hc hl.aligned)
      (fun _ _ _ _ ha hb => unique_byte_writer hp hw hc hl ha hb)
  · intro offset hoffset other otherValue hother
    have hown : candidate.view.writeByte writer (base.add offset) = some (Scalar.u32Byte value offset) := by
      simpa only [Ptx.Event.Candidate.writeByte,he,Option.bind_some,Ptx.Event.Kind.writeByte]
        using Scalar.u32_payload_byte base value offset hoffset
    exact unique_byte_writer hp hw hc hl hother hown

theorem all_completed_observed_arrays {mode input launch candidate rf co observation}
    (hp : KernelPre mode input launch) (hw : Shuffle.WellFormed (code mode) launch candidate)
    (hc : Shuffle.Complete candidate) (hd : Defined launch.geometry.block candidate)
    (ha : Agreement launch.geometry.block candidate)
    (hm : Ptx.Event.GenericMemoryConditions candidate.view launch.initial rf co)
    (ho : Ptx.Event.ObserverConditions candidate.view launch.initial rf co observation)
    (hcover : ArrayCovered input launch observation.domain) :
    ArrayValues mode input launch observation.output := by
  intro id hi
  obtain ⟨trace,ht,hid⟩ := hw.2.2.2 id hi
  have hv := agreed_stores_have_independent_values hp.1.2.1 hw hc hd ha ht
  rw [hid] at hv
  have hzero := output_location_layout hw.1 hp.2 hi (slot := 0) (by decide)
  have hfour := output_location_layout hw.1 hp.2 hi (slot := 4) (by decide)
  have hword := observe_unique_output_word hp.1.2.1 hw hc hp.2 hm ho hv.1 (by
    intro offset hoffset
    rw [hzero]
    simpa only [Location.add,Nat.add_zero] using hcover id hi offset (by omega))
  have hflag := observe_unique_output_word hp.1.2.1 hw hc hp.2 hm ho hv.2 (by
    intro offset hoffset
    rw [hfour]
    simpa only [Location.add,Nat.add_assoc] using hcover id hi (4+offset) (by omega))
  exact ⟨by simpa only [hzero,Nat.add_zero] using hword,by simpa only [hfour] using hflag⟩

theorem exported_output_contract (mode : Mode) (input : Inputs) (domain : Scalar.Launch → List Location)
    (hcover : ∀ launch, KernelPre mode input launch → ArrayCovered input launch (domain launch)) :
    Shuffle.Triple (code mode) (KernelPre mode input) domain (ArrayPost mode input domain) := by
  intro launch candidate rf co observation hp hw hc _ hd ha hm ho hdomain
  refine ⟨all_completed_observed_arrays hp hw hc hd ha hm ho ?_,?_⟩
  · rw [hdomain]
    exact hcover launch hp
  · intro loc hloc hout
    apply observer_frame_outside_output hp.1.2.1 hw hc hp.2.aligned ho
    · simpa only [hdomain] using hloc
    · exact fun hf => hout (output_footprint_in_array hw.1 hp.2 hf)

theorem exported_kernel_safe (mode : Mode) (input : Inputs) :
    Shuffle.Safe (code mode) (KernelPre mode input) := by
  intro launch candidate rf co hp hw hc hcontrol ha hm
  exact exported_source_safe mode input launch candidate rf co hp.1 hw hc hcontrol ha hm

def arrayDomain (input : Inputs) (launch : Scalar.Launch) : List Location :=
  (List.range (8*launch.geometry.block.volume)).map (fun offset => ⟨.global,input.out+offset⟩)

theorem array_domain_global (input : Inputs) (launch : Scalar.Launch) :
    ∀ loc ∈ arrayDomain input launch, loc.space = .global := by
  intro loc hloc
  obtain ⟨offset,_,rfl⟩ := List.mem_map.mp hloc
  rfl

theorem array_domain_covers {input launch} (hg : launch.geometry.Valid) :
    ArrayCovered input launch (arrayDomain input launch) := by
  intro id hi offset hoffset
  have hindex := Dim3.linear_lt_volume hg.2 hi.2
  apply List.mem_map.mpr
  refine ⟨8*linear launch.geometry.block id+offset,List.mem_range.mpr ?_,?_⟩
  · change linear launch.geometry.block id < launch.geometry.block.volume at hindex
    omega
  · simp only [Nat.add_assoc]

theorem exported_array_contract (mode : Mode) (input : Inputs) :
    Shuffle.Triple (code mode) (KernelPre mode input) (arrayDomain input) (ArrayPost mode input (arrayDomain input)) :=
  exported_output_contract mode input (arrayDomain input) (fun _ hp => array_domain_covers hp.1.1)

theorem exported_array_nonvacuous (mode : Mode) (input : Inputs) :
    Shuffle.Nonvacuous (code mode) (KernelPre mode input) (arrayDomain input) :=
  exported_kernel_nonvacuous mode input (arrayDomain input) (fun launch _ => array_domain_global input launch)

theorem exported_array_verified (mode : Mode) (input : Inputs) :
    Shuffle.Safe (code mode) (KernelPre mode input) ∧
    Shuffle.Triple (code mode) (KernelPre mode input) (arrayDomain input) (ArrayPost mode input (arrayDomain input)) ∧
    Shuffle.Nonvacuous (code mode) (KernelPre mode input) (arrayDomain input) :=
  ⟨exported_kernel_safe mode input,exported_array_contract mode input,exported_array_nonvacuous mode input⟩

theorem exported_observed_witness (mode : Mode) (input : Inputs) (domain : Scalar.Launch → List Location)
    (hg : ∀ launch, KernelPre mode input launch → ∀ loc ∈ domain launch, loc.space = .global)
    (hcover : ∀ launch, KernelPre mode input launch → ArrayCovered input launch (domain launch))
    (launch : Scalar.Launch) (hp : KernelPre mode input launch) :
    ∃ candidate rf co observation, Shuffle.WellFormed (code mode) launch candidate ∧ Shuffle.Complete candidate ∧
      ControlAdmitted launch.geometry.block candidate ∧ Defined launch.geometry.block candidate ∧
      Agreement launch.geometry.block candidate ∧ Ptx.Event.GenericMemoryConditions candidate.view launch.initial rf co ∧
      Ptx.Event.ObserverConditions candidate.view launch.initial rf co observation ∧ observation.domain = domain launch ∧
      ArrayPost mode input domain launch observation.output := by
  obtain ⟨candidate,rf,co,observation,hw,hc,hcontrol,hd,ha,hm,ho,hdom⟩ :=
    exported_kernel_nonvacuous mode input domain hg launch hp
  exact ⟨candidate,rf,co,observation,hw,hc,hcontrol,hd,ha,hm,ho,hdom,
    exported_output_contract mode input domain hcover launch candidate rf co observation hp hw hc hcontrol hd ha hm ho hdom⟩

end
end Ptx.Kernels.ShuffleProbe
