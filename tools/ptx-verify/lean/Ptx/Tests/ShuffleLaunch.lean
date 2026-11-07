import Ptx.Tests.ShuffleProbe
import Ptx.Kernels.ShuffleProbeMemoryWitness

/-! Static launch checks, partial-warp counterexamples, and a joined complete
source/control/collective/memory/observer witness for every supported mode. -/
namespace Ptx.ShuffleLaunchTests
open Ptx.ISA Ptx.Shuffle Ptx.Kernels.ShuffleProbe
open Ptx.ShuffleProbeTests
noncomputable section

def launch : Scalar.Launch := ⟨⟨.one,⟨4,4,4⟩⟩,bindings input,fun _ => .bits (byte 99)⟩
def multiLaunch : Scalar.Launch := {launch with geometry := ⟨⟨2,1,1⟩,⟨4,4,4⟩⟩}
def domain : List Location := [⟨.global,4096⟩,⟨.global,4099⟩,⟨.global,4100⟩,⟨.global,4103⟩,⟨.global,4607⟩,⟨.global,4608⟩]

theorem full_launch_pre (mode : Mode) : KernelPre mode input launch := by
  refine ⟨⟨?_,all_parameter_bindings input,?_⟩,⟨rfl,by decide,by decide,by decide⟩⟩
  · simp [launch,Geometry.Valid,Dim3.Positive,Dim3.one]
  · exact full_warps_launch_closed mode input _ (by decide) (by decide)

theorem multi_cta_source_safety_pre (mode : Mode) : SafePre mode input multiLaunch := by
  refine ⟨?_,all_parameter_bindings input,?_⟩
  · simp [multiLaunch,launch,Geometry.Valid,Dim3.Positive,Dim3.one]
  · exact full_warps_launch_closed mode input _ (by decide) (by decide)

theorem multi_cta_is_not_the_single_cta_output_layout : ¬LayoutPre input multiLaunch := by
  intro hp
  have h := congrArg Dim3.x hp.grid
  norm_num [multiLaunch,Dim3.one] at h

theorem all_modes_source_safe (mode : Mode) : Shuffle.Safe (code mode) (SafePre mode input) := exported_source_safe mode input

theorem joined_complete_execution_exists (mode : Mode) :
    ∃ candidate rf co observation, Shuffle.WellFormed (code mode) launch candidate ∧ Shuffle.Complete candidate ∧
      ControlAdmitted launch.geometry.block candidate ∧ Defined launch.geometry.block candidate ∧
      Agreement launch.geometry.block candidate ∧ Ptx.Event.GenericMemoryConditions candidate.view launch.initial rf co ∧
      Ptx.Event.ObserverConditions candidate.view launch.initial rf co observation ∧ observation.domain = domain := by
  apply exported_kernel_nonvacuous mode input (fun _ => domain) _ launch (full_launch_pre mode)
  intro _ _ loc hl
  simp only [domain,List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def partialInput (mode : Mode) : Inputs := {input with b := 1,c := if mode = .up then 0 else 15,mask := 0xffff}
theorem partial_warps_close_for_all_modes (mode : Mode) : LaunchClosed mode (partialInput mode) ⟨4,2,2⟩ := by
  cases mode <;> decide

def inactiveSourceInput : Inputs := {input with b := 1,c := 31,mask := 0xffffffff}
theorem partial_warp_inactive_source_is_rejected : ¬LaunchClosed .down inactiveSourceInput ⟨16,1,1⟩ := by decide
theorem partial_warp_unnamed_caller_is_rejected : ¬LaunchClosed .bfly {input with mask := 255} ⟨16,1,1⟩ := by decide

theorem empty_closure_is_not_a_legal_launch : LaunchClosed .bfly input ⟨0,1,1⟩ ∧
    ¬SafePre .bfly input {launch with geometry := ⟨.one,⟨0,1,1⟩⟩} := by
  refine ⟨by decide,?_⟩
  intro hp
  have h := hp.1.2.1
  norm_num [Dim3.Positive] at h

theorem wrapped_extent_is_not_a_valid_layout : ¬LayoutPre crossingInput launch := by
  intro hp
  have h := hp.extent
  norm_num [crossingInput,launch,Dim3.volume] at h

theorem three_dimensional_thread_enumeration_covers_64_threads : launch.geometry.threadIds.length = 64 := by
  simp [Geometry.threadIds,launch,Dim3.volume,Dim3.one]
theorem multi_cta_thread_enumeration_covers_128_threads : multiLaunch.geometry.threadIds.length = 128 := by
  simp [Geometry.threadIds,multiLaunch,Dim3.volume,Dim3.one]

end
end Ptx.ShuffleLaunchTests
