import Ptx.Kernels.HopperDoubleBufferPrefetch

/-! All actual next-tile prefetch paths from PC 61 to PC 76. Unused replies
are not constrained: payload-size premises apply only to producer prefetches.
All memory/resource/tensor admission still lies beyond these source runs. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def needsPrefetch (tile tiles : Nat) (leader : Bool) : Prop := tile+1 < tiles ∧ leader = true
instance (tile tiles : Nat) (leader : Bool) : Decidable (needsPrefetch tile tiles leader) :=
  inferInstanceAs (Decidable (tile+1 < tiles ∧ leader = true))
def preludeState (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) : Wgmma.State :=
  let guarded := prefetchGuardState s tile tiles leader
  if needsPrefetch tile tiles leader then prefetchState guarded tile (tile+1) else guarded
def preludeSteps (tile tiles : Nat) (leader : Bool) : Nat :=
  prefetchGuardSteps tile tiles+(if needsPrefetch tile tiles leader then prefetchSteps tile else 0)
def preludeEvents (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (tile tiles : Nat) (leader : Bool) (mapA mapB : Nat) : List Wgmma.Event :=
  if needsPrefetch tile tiles leader then
    prefetchTransferEvents ctx oracle (prefetchGuardState s tile tiles leader) (stage (tile+1)) (tile+1) mapA mapB
  else []

theorem prelude_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (tile tiles : Nat) (leader : Bool) (mapA mapB : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 61)
    (hp : Wgmma.pending s.ledger = [])
    (ht : lookup "%tile" s.base.scalar.core.thread.regs = some tile)
    (hb : lookup "%tiles" s.base.scalar.core.thread.regs = some tiles)
    (hl : lookup "%leader" s.base.scalar.core.thread.regs = some (if leader then 1 else 0))
    (he : lookup "%even" s.base.scalar.core.thread.regs = some (if tile%2 = 0 then 1 else 0))
    (hb0 : lookup "%bar0" s.base.scalar.core.thread.regs = some 0)
    (hb1 : lookup "%bar1" s.base.scalar.core.thread.regs = some 8)
    (hma : lookup "%mapa" s.base.scalar.core.thread.regs = some mapA)
    (hmb : lookup "%mapb" s.base.scalar.core.thread.regs = some mapB)
    (hlt : tile < tiles) (hbound : tiles ≤ 2^28)
    (hshape : needsPrefetch tile tiles leader →
      (oracle.base.tmaBytes (s.base.scalar.core.queries+1)).length = (oracle.base.descriptor s.base.scalar.core.queries).bytes ∧
      (oracle.base.tmaBytes (s.base.scalar.core.queries+3)).length = (oracle.base.descriptor (s.base.scalar.core.queries+2)).bytes) :
    Wgmma.run ctx oracle code (preludeSteps tile tiles leader) s =
      .ok (preludeState s tile tiles leader,preludeEvents ctx oracle s tile tiles leader mapA mapB) := by
  have hg := prefetch_guard_execute ctx oracle s tile tiles leader hr hpc hp ht hb hl hlt (by omega)
  rw [preludeSteps,Wgmma.run_add,hg]
  by_cases hn : needsPrefetch tile tiles leader
  · have hnext := hn.1
    have hproducer := hn.2
    have hpref := prefetch_execute ctx oracle (prefetchGuardState s tile tiles leader) tile (tile+1) mapA mapB
      (by simpa using hr) (by simp [hnext,hproducer]) (by simpa using hp)
      (by rwa [prefetchGuardState_nat_frame _ _ _ _ "%even" (by decide)])
      (by rwa [prefetchGuardState_nat_frame _ _ _ _ "%bar0" (by decide)])
      (by rwa [prefetchGuardState_nat_frame _ _ _ _ "%bar1" (by decide)])
      (prefetchGuardState_next s tile tiles leader)
      (by rwa [prefetchGuardState_nat_frame _ _ _ _ "%mapa" (by decide)])
      (by rwa [prefetchGuardState_nat_frame _ _ _ _ "%mapb" (by decide)]) (by omega)
      (by simpa using (hshape hn).1) (by simpa using (hshape hn).2)
    simp only [hn,ite_true,Except.bind,hpref,List.nil_append,preludeState,preludeEvents]
  · simp only [hn,ite_false,Except.bind,Wgmma.run,List.nil_append,preludeState,preludeEvents]

@[simp] theorem preludeState_pc (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) :
    (preludeState s tile tiles leader).base.scalar.core.thread.pc = 76 := by
  by_cases hn : needsPrefetch tile tiles leader
  · simp [preludeState,hn]
  · simp only [preludeState,hn,ite_false,prefetchGuardState_pc]
    by_cases ht : tile+1 < tiles
    · have hl : leader = false := by cases leader <;> simp_all [needsPrefetch]
      simp [ht,hl]
    · simp [ht]
@[simp] theorem preludeState_queries (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) :
    (preludeState s tile tiles leader).base.scalar.core.queries =
      s.base.scalar.core.queries+(if needsPrefetch tile tiles leader then 4 else 0) := by
  by_cases h : needsPrefetch tile tiles leader <;> simp [preludeState,h]
@[simp] theorem preludeState_status (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) :
    (preludeState s tile tiles leader).base.scalar.core.thread.status = s.base.scalar.core.thread.status := by
  by_cases h : needsPrefetch tile tiles leader <;> simp [preludeState,h]
@[simp] theorem preludeState_pending (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) :
    Wgmma.pending (preludeState s tile tiles leader).ledger = Wgmma.pending s.ledger := by
  by_cases h : needsPrefetch tile tiles leader <;> simp [preludeState,h]

theorem preludeState_nat_frame (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) (name : String)
    (hn : name ∉ ["%next","%more","%nextbar","%copya","%copyb","%ay"]) :
    lookup name (preludeState s tile tiles leader).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := by
  have hh : name ≠ "%next" ∧ name ≠ "%more" ∧ name ≠ "%nextbar" ∧ name ≠ "%copya" ∧ name ≠ "%copyb" ∧ name ≠ "%ay" := by simpa using hn
  by_cases h : needsPrefetch tile tiles leader
  · rw [preludeState,if_pos h,prefetchState_nat_frame,prefetchGuardState_nat_frame]
    all_goals simp [hh]
  · rw [preludeState,if_neg h,prefetchGuardState_nat_frame]
    simp [hh]

theorem preludeState_float_frame (s : Wgmma.State) (tile tiles : Nat) (leader : Bool) (name : String)
    (hx : name ∉ ["%next","%more","%nextbar","%copya","%copyb","%ay"])
    (hn : lookup name s.base.scalar.core.thread.regs = none) :
    declarationLookup name (preludeState s tile tiles leader).base.scalar.floats = declarationLookup name s.base.scalar.floats := by
  have hh : name ≠ "%next" ∧ name ≠ "%more" ∧ name ≠ "%nextbar" ∧ name ≠ "%copya" ∧ name ≠ "%copyb" ∧ name ≠ "%ay" := by simpa using hx
  have hg : name ∉ ["%next","%more"] := by simp [hh]
  by_cases h : needsPrefetch tile tiles leader
  · rw [preludeState,if_pos h,prefetchState_float_frame,prefetchGuardState_float_frame _ _ _ _ _ hg hn]
    · simp [hh]
    · rw [prefetchGuardState_nat_frame _ _ _ _ _ hg,hn]
  · rw [preludeState,if_neg h,prefetchGuardState_float_frame _ _ _ _ _ hg hn]

end
end Ptx.Kernels.HopperDoubleBuffer
