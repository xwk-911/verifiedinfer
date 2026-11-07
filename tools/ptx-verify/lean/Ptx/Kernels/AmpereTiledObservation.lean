import Ptx.Kernels.AmpereTiledMemory

/-! Bytewise final output and frame facts. Matrix accumulation correctness is
still separate: an admitted observer sees the actual final stores. -/
namespace Ptx.AmpereTiledObservation
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledGraph
noncomputable section

theorem eligible {cfg launch candidate} (h : SourceInfo cfg launch candidate) (rf : Ampere.ReadsFrom) (loc) :
    MemoryGraph.ObserverEligible candidate.memoryGraph rf loc :=
  MemoryGraph.race_free_observer_eligible (AmpereTiledRace.race_free h rf) loc

theorem output_store {cfg launch candidate rf co o writer loc value} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) (ho : ObserverConstraints candidate launch.initial rf co o)
    (hd : loc ∈ o.domain) (hs : loc.space = .global) (hw : candidate.writeByte writer loc = some value) :
    o.output loc = value :=
  MemoryGraph.observer_unique_writer hm ho hd (eligible h rf loc) hw
    (fun _ _ hother => AmpereTiledGlobalAccesses.global_writer_unique h hs hother hw)

theorem frame {cfg launch candidate rf co o} (h : SourceInfo cfg launch candidate)
    (ho : ObserverConstraints candidate launch.initial rf co o) (hd : o.domain = domain cfg)
    {loc} (hl : loc ∈ domain cfg) (hn : ¬ InOutput cfg loc) : o.output loc = launch.initial loc := by
  have hs := domain_global hl
  apply MemoryGraph.observer_unwritten ho (hd ▸ hl) (eligible h rf loc)
  intro writer
  cases hw : candidate.writeByte writer loc with
  | none => exact hw
  | some value => exact (hn (AmpereTiledGlobalAccesses.global_write_region h hs hw)).elim

end
end Ptx.AmpereTiledObservation
