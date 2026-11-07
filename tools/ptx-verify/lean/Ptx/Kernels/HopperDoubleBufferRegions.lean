import Ptx.Hopper.RegionLoans
import Ptx.Kernels.HopperDoubleBufferRetryTensorInputs

/-! Source-derived region coverage for one native collective and A transfer.
The regions describe exact modeled byte locations; concrete allocation/runtime
ownership and functional byte-value simulation are separate obligations. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def regionA (tile : Nat) : Regions.Region := ⟨⟨.shared .zero,aBase (stage tile)⟩,2048⟩
def regionB (tile : Nat) : Regions.Region := ⟨⟨.shared .zero,bBase (stage tile)⟩,256⟩
def regionDescriptorA : Regions.Region := ⟨⟨.global,4096⟩,128⟩
def regionInputA (tiles : Nat) : Regions.Region := ⟨⟨.global,65536⟩,2048*tiles⟩

private theorem a_view_region_bytes (tiles : Nat) : (aView 65536 tiles).bytes = 2048 := by
  norm_num [aView,Tma.Descriptor2D.bytes]

def nativeBindings (work : Work) (tile : Nat) : List Regions.Binding :=
  [⟨work,⟨0,1⟩,0,.read,regionA tile⟩,⟨work,⟨0,2⟩,1,.read,regionB tile⟩]
def tmaABindings (work : Work) (tiles tile : Nat) : List Regions.Binding :=
  [⟨work,⟨0,1⟩,0,.read,regionDescriptorA⟩,⟨work,⟨0,2⟩,1,.read,regionInputA tiles⟩,⟨work,⟨0,2⟩,2,.write,regionA tile⟩]
def regionPlan (work : Work) : Bridge.Plan := fun ticket => if ticket = ⟨0,1⟩ ∨ ticket = ⟨0,2⟩ then some work else none
def nativeLayout (tile : Nat) : Regions.Layout := fun bid => [regionA tile,regionB tile][bid]?
def tmaALayout (tiles tile : Nat) : Regions.Layout := fun bid => [regionDescriptorA,regionInputA tiles,regionA tile][bid]?

theorem native_layout_separated (tile : Nat) : Regions.Separated (nativeLayout tile) := by
  intro left right a b ha hb hne loc hla hlb
  rcases left with _ | (_ | left) <;> rcases right with _ | (_ | right) <;>
    simp only [nativeLayout,List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,Option.some.injEq] at ha hb
  all_goals try cases ha
  all_goals try cases hb
  all_goals try exact hne rfl
  all_goals
    have hbound := (stage_arena_bounds (stage tile)).2.2.1
    simp only [Regions.Region.Contains,regionA,regionB] at hla hlb
    omega

theorem tma_a_layout_separated (tiles tile : Nat) : Regions.Separated (tmaALayout tiles tile) := by
  intro left right a b ha hb hne loc hla hlb
  rcases left with _ | (_ | (_ | left)) <;> rcases right with _ | (_ | (_ | right)) <;>
    simp only [tmaALayout,List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,Option.some.injEq] at ha hb
  all_goals try cases ha
  all_goals try cases hb
  all_goals try exact hne rfl
  all_goals simp only [Regions.Region.Contains,regionDescriptorA,regionInputA,regionA] at hla hlb
  all_goals first | (solve | omega) | (exact AddressSpace.noConfusion (hla.1.symm.trans hlb.1))

theorem native_bindings_mapped (work tile) : Regions.Mapped (nativeLayout tile) (regionPlan work) (nativeBindings work tile) := by
  simp [Regions.Mapped,nativeBindings,nativeLayout,regionPlan]

theorem tma_a_bindings_mapped (work tiles tile) : Regions.Mapped (tmaALayout tiles tile) (regionPlan work) (tmaABindings work tiles tile) := by
  simp [Regions.Mapped,tmaABindings,tmaALayout,regionPlan]

theorem native_use_regions {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles)
    {control node loc mode}
    (hu : Use Tma.localShared Access.globalDescriptor candidate (.native (family.mmaId tile 0)) control node loc mode) :
    mode = .read ∧ ((regionA tile).Contains loc ∨ (regionB tile).Contains loc) := by
  cases hu with
  | nativeRead hr =>
    have he := Unified.collective_representative (familyCollective family hw tile ht)
    have hp := Option.some.inj (hr.symm.trans he)
    cases hp
    refine ⟨rfl,?_⟩
    rename_i operand
    cases operand with
    | a p part =>
      left
      change (regionA tile).Contains (Wgmma.operandLocation .zero (family.calls tile 0) (.a p part))
      rw [show Wgmma.operandLocation .zero (family.calls tile 0) (.a p part) = _ from
        reply_operand_a_location tiles 0 (family.replies 0) (family.schedules 0) tile p part]
      exact ⟨rfl,by dsimp [regionA]; omega,by dsimp [regionA]; exact Nat.add_lt_add_left (Wgmma.aOffset (p,part)).isLt _⟩
    | b p part =>
      right
      change (regionB tile).Contains (Wgmma.operandLocation .zero (family.calls tile 0) (.b p part))
      rw [show Wgmma.operandLocation .zero (family.calls tile 0) (.b p part) = _ from
        reply_operand_b_location tiles 0 (family.replies 0) (family.schedules 0) tile p part]
      exact ⟨rfl,by dsimp [regionB]; omega,by dsimp [regionB]; exact Nat.add_lt_add_left (Wgmma.bOffset (p,part)).isLt _⟩

theorem tma_a_use_regions {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28) (tile : Nat) (ht : tile < tiles)
    {control node loc mode}
    (hu : Use Tma.localShared Access.globalDescriptor candidate (.tma (family.copyAId tile)) control node loc mode) :
    (mode = .read ∧ (regionDescriptorA.Contains loc ∨ (regionInputA tiles).Contains loc)) ∨
      (mode = .write ∧ (regionA tile).Contains loc) := by
  have hc := family_copy_a_at family hw tile ht
  cases hu with
  | descriptor actual ho =>
    have heq := Option.some.inj (actual.symm.trans hc)
    subst_vars
    left
    refine ⟨rfl,.inl ?_⟩
    rw [reply_copy_a_descriptor_address]
    exact ⟨rfl,by dsimp [regionDescriptorA,Access.globalDescriptor,Location.add]; omega,
      by dsimp [regionDescriptorA,Access.globalDescriptor,Location.add]; omega⟩
  | tmaRead hl hv =>
    rename_i offset value
    have hbnd := read_write_present hl
    simp only [Tma.WritePresent,hc,family_copy_a_descriptor family hw hd tile ht] at hbnd
    rw [a_view_region_bytes] at hbnd
    have hsource := retry_copy_a_source_byte family hw hd hb tile ht ⟨offset,hbnd⟩
    have hloc : loc = ⟨.global,65536+2048*tile+offset⟩ := by
      simpa only [Tma.readLocation,hc,Option.bind_some,hsource,Option.some.injEq] using hl.symm
    rw [hloc]
    left
    refine ⟨rfl,.inr ⟨rfl,by dsimp [regionInputA]; omega,?_⟩⟩
    dsimp [regionInputA] at *
    omega
  | tmaWrite hl hv =>
    rename_i offset value
    have hbnd := location_write_present hl
    simp only [Tma.WritePresent,hc,family_copy_a_descriptor family hw hd tile ht] at hbnd
    rw [a_view_region_bytes] at hbnd
    have hloc := retry_transfer_a_location family hw hd tile ht ⟨offset,hbnd⟩
    have heq : loc = _ := Option.some.inj (hl.symm.trans hloc)
    rw [heq]
    right
    exact ⟨rfl,rfl,by dsimp [regionA]; omega,by dsimp [regionA]; exact Nat.add_lt_add_left hbnd _⟩

theorem native_region_coverage {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (tile : Nat) (ht : tile < tiles) :
    Regions.Covers Tma.localShared Access.globalDescriptor candidate (fun work => work = .native (family.mmaId tile 0))
      (nativeBindings (.native (family.mmaId tile 0)) tile) := by
  intro work control node loc mode heq hu
  subst work
  obtain ⟨rfl,ha | hb⟩ := native_use_regions family hw tile ht hu
  · exact ⟨⟨_,⟨0,1⟩,0,.read,regionA tile⟩,by simp [nativeBindings],rfl,rfl,ha⟩
  · exact ⟨⟨_,⟨0,2⟩,1,.read,regionB tile⟩,by simp [nativeBindings],rfl,rfl,hb⟩

theorem tma_a_region_coverage {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28) (tile : Nat) (ht : tile < tiles) :
    Regions.Covers Tma.localShared Access.globalDescriptor candidate (fun work => work = .tma (family.copyAId tile))
      (tmaABindings (.tma (family.copyAId tile)) tiles tile) := by
  intro work control node loc mode heq hu
  subst work
  rcases tma_a_use_regions family hw hd hb tile ht hu with ⟨rfl,ha | hb⟩ | ⟨rfl,hc⟩
  · exact ⟨⟨_,⟨0,1⟩,0,.read,regionDescriptorA⟩,by simp [tmaABindings],rfl,rfl,ha⟩
  · exact ⟨⟨_,⟨0,2⟩,1,.read,regionInputA tiles⟩,by simp [tmaABindings],rfl,rfl,hb⟩
  · exact ⟨⟨_,⟨0,2⟩,2,.write,regionA tile⟩,by simp [tmaABindings],rfl,rfl,hc⟩

end
end Ptx.Kernels.HopperDoubleBuffer
