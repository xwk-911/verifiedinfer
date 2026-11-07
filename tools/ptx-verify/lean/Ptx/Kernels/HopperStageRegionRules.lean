import Ptx.Kernels.HopperStageAccessRegions

/-! Region arithmetic shared by the one-stage and repeated kernels. A writer
is a shared byte or aligned output word. Any overlapping admitted access has
the same complete footprint; input and descriptor regions are disjoint. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA

theorem overlapping_regions_equal {wb rb : Location} {ws rs : Nat} {loc : Location}
    (hwreg : SharedByte wb ws ∨ OutputWord wb ws) (hrreg : Region rb rs)
    (hwb : wb.space = loc.space ∧ wb.address ≤ loc.address ∧ loc.address < wb.address+ws)
    (hrb : rb.space = loc.space ∧ rb.address ≤ loc.address ∧ loc.address < rb.address+rs) :
    wb = rb ∧ ws = rs := by
  rcases loc with ⟨lspace,laddr⟩
  rcases hwb with ⟨hwspace,hwlower,hwupper⟩
  rcases hrb with ⟨hrspace,hrlower,hrupper⟩
  have hspace := hwspace.trans hrspace.symm
  rcases wb with ⟨wspace,waddr⟩
  rcases rb with ⟨rspace,raddr⟩
  change wspace = rspace at hspace
  subst rspace
  simp only [SharedByte,OutputWord,Region,Location.mk.injEq] at hwreg hrreg ⊢
  rcases hwreg with ⟨hws,hwn⟩ | ⟨hws,hwn,hwl,hwu,hwa⟩
  all_goals rcases hrreg with ⟨hrs,hrn⟩ | ⟨hrs,hrn,hrl,hru,hra⟩ | ⟨hrs,hrn,hrl⟩ | ⟨hrs,hrn,hru⟩
  all_goals simp_all
  all_goals grind

end Ptx.Kernels.HopperStage
