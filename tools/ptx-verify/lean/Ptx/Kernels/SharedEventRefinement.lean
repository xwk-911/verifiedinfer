import Ptx.Kernels.SharedEventWitness
import Ptx.Kernels.SharedCompletion

/-! Event-to-operational output inclusion for ORIGINAL SharedSwap configurations.
The same region encoding rules used by Copy retain arbitrary unknown frame bytes.
Completion includes the actual full-CTA release and produces replayable schedules.
The explicit memory/observer predicates remain relative to the current subset.
-/
namespace Ptx.SharedEvent
open Ptx.ISA Ptx.Event

theorem region_cell_post (c : SharedContract.Config) {m : Machine} (hm : SharedContract.Post c m) :
    Cells.RegionCellPost c.before m.globalMem c.dst 2 (fun i => CopyContract.word (c.input (SharedContract.other i))) := by
  refine ⟨hm.size,hm.values,?_⟩
  intro cell hout
  exact hm.frame cell (by simpa only [CopyContract.Outside,Cells.Outside,c.n_two] using hout)

theorem region_byte_post (c : SharedContract.Config) {initial output : ByteMap} (hb : BytePost c initial output) :
    Cells.RegionBytePost c.before.length c.dst 2 (fun i => CopyContract.word (c.input (SharedContract.other i))) initial output := by
  refine ⟨hb.1,?_⟩
  intro loc hmem hout
  exact hb.2 loc hmem (by simpa only [Cells.Destination,CopyEvent.Destination,c.n_two] using hout)

theorem represents_cell_post (c : SharedContract.Config) {initial output : ByteMap} {m : Machine}
    (hi : Cells.Represents c.before initial) (hb : BytePost c initial output) (hm : SharedContract.Post c m) :
    Cells.Represents m.globalMem output :=
  Cells.region_represents hi (region_byte_post c hb) (region_cell_post c hm)

theorem domain_post_encoding_agreement (c : SharedContract.Config) {initial output : ByteMap} {m : Machine}
    (hi : Cells.Represents c.before initial) (hb : BytePost c initial output) (hm : SharedContract.Post c m)
    (loc : Location) (hmem : loc ∈ domain c) : output loc = Cells.encode m.globalMem initial loc :=
  Cells.region_domain_encoding hi (region_byte_post c hb) (region_cell_post c hm) loc hmem

theorem completed_output_agreement (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    {sources : ReadsFrom} {order : Coherence} {o : Observation} {m m' : Machine}
    (hp : Pre c l) (hw : execution.WellFormed code l)
    (hc : GenericMemoryConditions execution l.initial sources order)
    (ho : ObserverConditions execution l.initial sources order o) (hd : o.domain = domain c)
    (hpre : SharedContract.Pre c m) (hs : Steps code m m')
    (hdone : m'.threads.all (fun t => t.status == .done) = true) :
    ∀ loc ∈ domain c, o.output loc = Cells.encode m'.globalMem l.initial loc :=
  domain_post_encoding_agreement c hp.2.2 (Event.triple_apply (correct c) hp hw hc ho hd)
    (SharedContract.correct c m m' hpre hs hdone)

theorem output_inclusion (c : SharedContract.Config) {l : Launch} {execution : Candidate}
    {sources : ReadsFrom} {order : Coherence} {o : Observation} {m : Machine}
    (hp : Pre c l) (hw : execution.WellFormed code l)
    (hc : GenericMemoryConditions execution l.initial sources order)
    (ho : ObserverConditions execution l.initial sources order o) (hd : o.domain = domain c)
    (hpre : SharedContract.Pre c m) :
    ∃ actions m', run code actions m = .ok m' ∧
      m'.threads.all (fun t => t.status == .done) = true ∧ SharedContract.Post c m' ∧
      ∀ loc ∈ domain c, o.output loc = Cells.encode m'.globalMem l.initial loc := by
  obtain ⟨m',hs,hdone,hpost⟩ := SharedCompletion.complete_from_pre hpre
  obtain ⟨actions,hrun⟩ := Termination.steps_run hs
  exact ⟨actions,m',hrun,hdone,hpost,domain_post_encoding_agreement c hp.2.2
    (Event.triple_apply (correct c) hp hw hc ho hd) hpost⟩

end Ptx.SharedEvent
