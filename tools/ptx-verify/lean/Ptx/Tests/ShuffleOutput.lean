import Ptx.Tests.ShuffleLaunch
import Ptx.Kernels.ShuffleProbeOutput

/-! Actual full/partial-warp launches, all four modes, full output domains and
guard bytes, joined correctness/non-vacuity, and initially incorrect bytes. -/
namespace Ptx.ShuffleOutputTests
open Ptx.ISA Ptx.Shuffle Ptx.Kernels.ShuffleProbe
open Ptx.ShuffleProbeTests Ptx.ShuffleLaunchTests
noncomputable section

def framedDomain (launch : Scalar.Launch) : List Location :=
  arrayDomain input launch ++ [⟨.global,4095⟩,⟨.global,4608⟩]

theorem framed_domain_covers {launch : Scalar.Launch} (hg : launch.geometry.Valid) :
    ArrayCovered input launch (framedDomain launch) := by
  intro id hi offset hoffset
  exact List.mem_append.mpr (Or.inl (array_domain_covers hg id hi offset hoffset))

theorem framed_domain_global (launch : Scalar.Launch) : ∀ loc ∈ framedDomain launch, loc.space = .global := by
  intro loc hloc
  rcases List.mem_append.mp hloc with harray | hframe
  · exact array_domain_global input launch loc harray
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hframe
    rcases hframe with rfl | rfl <;> rfl

theorem all_modes_output_and_guards (mode : Mode) :
    Shuffle.Triple (code mode) (KernelPre mode input) framedDomain (ArrayPost mode input framedDomain) :=
  exported_output_contract mode input framedDomain (fun _ hp => framed_domain_covers hp.1.1)

theorem complete_observed_output_exists_for_all_modes (mode : Mode) :
    ∃ candidate rf co observation, Shuffle.WellFormed (code mode) launch candidate ∧ Shuffle.Complete candidate ∧
      ControlAdmitted launch.geometry.block candidate ∧ Defined launch.geometry.block candidate ∧
      Agreement launch.geometry.block candidate ∧ Ptx.Event.GenericMemoryConditions candidate.view launch.initial rf co ∧
      Ptx.Event.ObserverConditions candidate.view launch.initial rf co observation ∧ observation.domain = framedDomain launch ∧
      ArrayPost mode input framedDomain launch observation.output :=
  exported_observed_witness mode input framedDomain (fun launch _ => framed_domain_global launch)
    (fun _ hp => framed_domain_covers hp.1.1) launch (full_launch_pre mode)

def first : ThreadId := ⟨.zero,.zero⟩
theorem first_thread_is_valid : first.Valid launch.geometry := by
  norm_num [first,launch,ThreadId.Valid,Dim3.Within,Dim3.one,Dim3.zero]

theorem first_output_byte_is_independent {mode output} (hp : ArrayValues mode input launch output) :
    output ⟨.global,4096⟩ = Scalar.u32Byte (expectedWord mode input (context launch first)) 0 := by
  simpa only [input,launch,first,linear,Dim3.linear,Dim3.zero,Location.add,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
    using (hp first first_thread_is_valid).1 0 (by decide)

theorem correct_first_byte_is_not_initial_99 (mode : Mode) :
    Scalar.u32Byte (expectedWord mode input (context launch first)) 0 ≠ launch.initial ⟨.global,4096⟩ := by
  have hbyte : Ptx.Event.Cells.wordByte (expectedWord mode input (context launch first)) 0 ≠ byte 99 := by
    cases mode <;> decide
  exact fun he => hbyte (Symbolic.Byte.bits.inj he)

theorem arbitrary_completed_observer_overwrites_initial_99 {mode candidate rf co observation}
    (hw : Shuffle.WellFormed (code mode) launch candidate) (hc : Shuffle.Complete candidate)
    (hcontrol : ControlAdmitted launch.geometry.block candidate) (hd : Defined launch.geometry.block candidate)
    (ha : Agreement launch.geometry.block candidate)
    (hm : Ptx.Event.GenericMemoryConditions candidate.view launch.initial rf co)
    (ho : Ptx.Event.ObserverConditions candidate.view launch.initial rf co observation)
    (hdom : observation.domain = framedDomain launch) :
    observation.output ⟨.global,4096⟩ ≠ launch.initial ⟨.global,4096⟩ := by
  have hp := all_modes_output_and_guards mode launch candidate rf co observation (full_launch_pre mode)
    hw hc hcontrol hd ha hm ho hdom
  rw [first_output_byte_is_independent hp.1]
  exact correct_first_byte_is_not_initial_99 mode

theorem guard_intervals_are_preserved {mode output} (hp : ArrayPost mode input framedDomain launch output) :
    output ⟨.global,4095⟩ = launch.initial ⟨.global,4095⟩ ∧
    output ⟨.global,4608⟩ = launch.initial ⟨.global,4608⟩ := by
  constructor
  · apply hp.2 _ (List.mem_append.mpr (Or.inr (by simp)))
    norm_num [ArrayFootprint,input,launch,Dim3.volume]
  · apply hp.2 _ (List.mem_append.mpr (Or.inr (by simp)))
    norm_num [ArrayFootprint,input,launch,Dim3.volume]

def partialLaunch (mode : Mode) : Scalar.Launch :=
  ⟨⟨.one,⟨4,2,2⟩⟩,bindings (partialInput mode),fun _ => .bits (byte 99)⟩

theorem partial_launch_pre (mode : Mode) : KernelPre mode (partialInput mode) (partialLaunch mode) := by
  refine ⟨⟨?_,all_parameter_bindings _,partial_warps_close_for_all_modes mode⟩,
    ⟨rfl,?_,?_,?_⟩⟩
  · simp [partialLaunch,Geometry.Valid,Dim3.Positive,Dim3.one]
  · change 16 ≤ 2^32
    decide
  · change 4096 % 4 = 0
    decide
  · change 4096+8*16 ≤ 2^64
    decide

theorem partial_warp_array_verified (mode : Mode) :
    Shuffle.Safe (code mode) (KernelPre mode (partialInput mode)) ∧
    Shuffle.Triple (code mode) (KernelPre mode (partialInput mode)) (arrayDomain (partialInput mode))
      (ArrayPost mode (partialInput mode) (arrayDomain (partialInput mode))) ∧
    Shuffle.Nonvacuous (code mode) (KernelPre mode (partialInput mode)) (arrayDomain (partialInput mode)) :=
  exported_array_verified mode (partialInput mode)

theorem exact_domain_has_all_512_bytes : (arrayDomain input launch).length = 512 := by
  simp [arrayDomain,launch,Dim3.volume]

theorem incomplete_old_probe_domain_is_rejected : ¬ArrayCovered input launch domain := by
  intro hp
  have h := hp first first_thread_is_valid 1 (by decide)
  norm_num [domain,input,launch,first,linear,Dim3.linear,Dim3.zero] at h

end
end Ptx.ShuffleOutputTests
