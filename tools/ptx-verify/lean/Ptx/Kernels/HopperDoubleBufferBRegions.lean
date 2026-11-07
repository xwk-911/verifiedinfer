import Ptx.Kernels.HopperDoubleBufferRegions

/-! B transfers use a different descriptor, global input base and 256-byte
shared destination. Their exact read/write coverage reuses the same loan rules.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper Ptx.Hopper.Progress
noncomputable section

def regionDescriptorB : Regions.Region := ⟨⟨.global,4224⟩,128⟩
def regionInputB (tiles : Nat) : Regions.Region := ⟨⟨.global,dataBBase tiles⟩,256*tiles⟩
def tmaBBindings (work : Work) (tiles tile : Nat) : List Regions.Binding :=
  [⟨work,⟨0,1⟩,0,.read,regionDescriptorB⟩,⟨work,⟨0,2⟩,1,.read,regionInputB tiles⟩,⟨work,⟨0,2⟩,2,.write,regionB tile⟩]

private theorem b_view_region_bytes (tiles : Nat) : (bView (dataBBase tiles) tiles).bytes = 256 := by
  norm_num [bView,Tma.Descriptor2D.bytes]

theorem tma_b_use_regions {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28) (tile : Nat) (ht : tile < tiles)
    {control node loc mode}
    (hu : Use Tma.localShared Access.globalDescriptor candidate (.tma (family.copyBId tile)) control node loc mode) :
    (mode = .read ∧ (regionDescriptorB.Contains loc ∨ (regionInputB tiles).Contains loc)) ∨
      (mode = .write ∧ (regionB tile).Contains loc) := by
  have hc := family_copy_b_at family hw tile ht
  cases hu with
  | descriptor actual ho =>
    have heq := Option.some.inj (actual.symm.trans hc)
    subst_vars
    left
    refine ⟨rfl,.inl ?_⟩
    rw [reply_copy_b_descriptor_address]
    exact ⟨rfl,by dsimp [regionDescriptorB,Access.globalDescriptor,Location.add]; omega,
      by dsimp [regionDescriptorB,Access.globalDescriptor,Location.add]; omega⟩
  | tmaRead hl hv =>
    rename_i offset value
    have hbnd := read_write_present hl
    simp only [Tma.WritePresent,hc,family_copy_b_descriptor family hw hd tile ht] at hbnd
    rw [b_view_region_bytes] at hbnd
    have hsource := retry_copy_b_source_byte family hw hd hb tile ht ⟨offset,hbnd⟩
    have hloc : loc = ⟨.global,dataBBase tiles+256*tile+offset⟩ := by
      simpa only [Tma.readLocation,hc,Option.bind_some,hsource,Option.some.injEq] using hl.symm
    rw [hloc]
    left
    refine ⟨rfl,.inr ⟨rfl,by dsimp [regionInputB]; omega,?_⟩⟩
    dsimp [regionInputB]
    omega
  | tmaWrite hl hv =>
    rename_i offset value
    have hbnd := location_write_present hl
    simp only [Tma.WritePresent,hc,family_copy_b_descriptor family hw hd tile ht] at hbnd
    rw [b_view_region_bytes] at hbnd
    have hloc := retry_transfer_b_location family hw hd tile ht ⟨offset,hbnd⟩
    have heq : loc = _ := Option.some.inj (hl.symm.trans hloc)
    rw [heq]
    right
    exact ⟨rfl,rfl,by dsimp [regionB]; omega,by dsimp [regionB]; exact Nat.add_lt_add_left hbnd _⟩

theorem tma_b_region_coverage {tiles initial candidate} (family : ReplySourceFamily tiles candidate)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate)
    (hd : Tma.DescriptorAgreement candidate.view (dataMaps tiles)) (hb : tiles ≤ 2^28) (tile : Nat) (ht : tile < tiles) :
    Regions.Covers Tma.localShared Access.globalDescriptor candidate (fun work => work = .tma (family.copyBId tile))
      (tmaBBindings (.tma (family.copyBId tile)) tiles tile) := by
  intro work control node loc mode heq hu
  subst work
  rcases tma_b_use_regions family hw hd hb tile ht hu with ⟨rfl,ha | hb⟩ | ⟨rfl,hc⟩
  · exact ⟨⟨_,⟨0,1⟩,0,.read,regionDescriptorB⟩,by simp [tmaBBindings],rfl,rfl,ha⟩
  · exact ⟨⟨_,⟨0,2⟩,1,.read,regionInputB tiles⟩,by simp [tmaBBindings],rfl,rfl,hb⟩
  · exact ⟨⟨_,⟨0,2⟩,2,.write,regionB tile⟩,by simp [tmaBBindings],rfl,rfl,hc⟩

end
end Ptx.Kernels.HopperDoubleBuffer
