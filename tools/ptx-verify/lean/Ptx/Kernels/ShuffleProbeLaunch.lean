import Ptx.Kernels.ShuffleProbeControl

/-! General full-warp closure, with a finite checker retained for partial warps
and dynamic b/c/mask values. No oracle or execution property is assumed. -/
namespace Ptx.Kernels.ShuffleProbe
open Ptx.ISA Ptx.Shuffle
noncomputable section

theorem full_mask_names_every_lane : ∀ which : Lane, member 0xffffffff which = true := by decide

theorem full_warps_launch_closed (mode : Mode) (input : Inputs) (block : Dim3)
    (hm : w32 input.mask = 0xffffffff) (hv : block.volume % 32 = 0) : LaunchClosed mode input block := by
  intro index
  refine ⟨?_,?_⟩
  · rw [hm]
    exact full_mask_names_every_lane _
  · have hi := index.isLt
    have hs := (select mode (BitVec.ofNat 5 index.val) (w32 input.b) (w32 input.c)).source.isLt
    have hd := Nat.mod_add_div block.volume 32
    omega

end
end Ptx.Kernels.ShuffleProbe
