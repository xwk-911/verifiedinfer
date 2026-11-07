import Ptx.Kernels.HopperDoubleBufferPrelude
import Ptx.Kernels.HopperDoubleBufferTransferReconstruction

/-! Invert the generated prefetch prelude with arbitrary replies. Payload
lengths follow from the actual completed source run; skipped producer paths
place no constraints on unused replies. Transfer values/admission are separate.
-/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def PreludeRegisters (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) (mapA mapB : Nat) : Prop :=
  lookup "%tile" s.base.scalar.core.thread.regs = some tile ∧
  lookup "%tiles" s.base.scalar.core.thread.regs = some tiles ∧
  lookup "%leader" s.base.scalar.core.thread.regs = some (if leader then 1 else 0) ∧
  lookup "%even" s.base.scalar.core.thread.regs = some (if tile%2 = 0 then 1 else 0) ∧
  lookup "%bar0" s.base.scalar.core.thread.regs = some 0 ∧ lookup "%bar1" s.base.scalar.core.thread.regs = some 8 ∧
  lookup "%mapa" s.base.scalar.core.thread.regs = some mapA ∧ lookup "%mapb" s.base.scalar.core.thread.regs = some mapB

theorem completed_prelude_shapes {ctx oracle s count last events tile tiles leader mapA mapB}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 61)
    (hp : Wgmma.pending s.ledger = []) (hregs : PreludeRegisters s tile tiles leader mapA mapB)
    (hlt : tile < tiles) (hbound : tiles ≤ 2^28)
    (hn : Wgmma.run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    needsPrefetch tile tiles leader →
      (oracle.base.tmaBytes (s.base.scalar.core.queries+1)).length = (oracle.base.descriptor s.base.scalar.core.queries).bytes ∧
      (oracle.base.tmaBytes (s.base.scalar.core.queries+3)).length = (oracle.base.descriptor (s.base.scalar.core.queries+2)).bytes := by
  intro hneeds
  obtain ⟨ht,hT,hl,he,hb0,hb1,hma,_⟩ := hregs
  have hguard := prefetch_guard_execute ctx oracle s tile tiles leader hr hpc hp ht hT hl hlt (by omega)
  have hgc := Wgmma.completed_after_running_prefix hn hd hguard (by simpa using hr)
  obtain ⟨guardTail,hg,_⟩ := Wgmma.run_suffix_of_prefix (Nat.le_of_lt hgc) hn hguard
  have haddr := prefetch_addresses_execute ctx oracle (prefetchGuardState s tile tiles leader) tile (tile+1)
    (by simpa using hr) (by simp [hneeds.1,hneeds.2]) (by simpa using hp)
    (by rwa [prefetchGuardState_nat_frame _ _ _ _ "%even" (by decide)])
    (by rwa [prefetchGuardState_nat_frame _ _ _ _ "%bar0" (by decide)])
    (by rwa [prefetchGuardState_nat_frame _ _ _ _ "%bar1" (by decide)])
    (prefetchGuardState_next s tile tiles leader) (by omega)
  have hac := Wgmma.completed_after_running_prefix hg hd haddr (by simpa using hr)
  obtain ⟨addrTail,ha,_⟩ := Wgmma.run_suffix_of_prefix (Nat.le_of_lt hac) hg haddr
  obtain ⟨hbar,hcopya,_,hay⟩ := prefetchAddressState_operands (prefetchGuardState s tile tiles leader) tile (tile+1)
  have hs := completed_transfer_shapes (by simpa using hr) (prefetchAddressState_pc _ _ _) (by simpa using hp)
    hbar hcopya
    (by rw [prefetchAddressState_nat_frame _ _ _ "%mapa" (by decide),prefetchGuardState_nat_frame _ _ _ _ "%mapa" (by decide)]; exact hma)
    hay ha hd
  simpa only [prefetchAddressState_queries,prefetchGuardState_queries] using hs

theorem completed_prelude_reconstruct {ctx oracle s count last events tile tiles leader mapA mapB}
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 61)
    (hp : Wgmma.pending s.ledger = []) (hregs : PreludeRegisters s tile tiles leader mapA mapB)
    (hlt : tile < tiles) (hbound : tiles ≤ 2^28)
    (hn : Wgmma.run ctx oracle code count s = .ok (last,events)) (hd : last.base.scalar.core.thread.status = .done) :
    preludeSteps tile tiles leader < count ∧
      ∃ tailEvents, Wgmma.run ctx oracle code (count-preludeSteps tile tiles leader) (preludeState s tile tiles leader) = .ok (last,tailEvents) ∧
        events = preludeEvents ctx oracle s tile tiles leader mapA mapB++tailEvents := by
  have hshape := completed_prelude_shapes hr hpc hp hregs hlt hbound hn hd
  obtain ⟨ht,hT,hl,he,hb0,hb1,hma,hmb⟩ := hregs
  have hprefix := prelude_execute ctx oracle s tile tiles leader mapA mapB hr hpc hp ht hT hl he hb0 hb1 hma hmb hlt hbound hshape
  have hc := Wgmma.completed_after_running_prefix hn hd hprefix (by simpa using hr)
  exact ⟨hc,Wgmma.run_suffix_of_prefix (Nat.le_of_lt hc) hn hprefix⟩

end
end Ptx.Kernels.HopperDoubleBuffer
