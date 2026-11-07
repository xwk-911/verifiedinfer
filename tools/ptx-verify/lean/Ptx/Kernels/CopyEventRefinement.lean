import Ptx.Kernels.CopyEventWitness
import Ptx.Kernels.CopyCompletion

/-! Output inclusion for the ORIGINAL Copy Config/Params and generated program.
Every permitted event observation is the byte encoding of an actual completed
operational execution. The observer and memory-model conditions remain explicit;
this is not a correspondence theorem for the full NVIDIA PTX memory model.
-/
namespace Ptx.CopyEvent
open Ptx.ISA Ptx.Event

theorem domain_post_encoding_agreement (c : CopyContract.Config) {initial output : ByteMap} {m : Machine}
    (hi : Cells.Represents c.before initial) (hb : BytePost c initial output) (hm : CopyContract.Post c m)
    (loc : Location) (hmem : loc ∈ domain c) : output loc = Cells.encode m.globalMem initial loc :=
  Cells.region_domain_encoding (dst := c.dst) (count := c.n) (values := fun i => CopyContract.word (c.input i))
    hi ⟨hb.1,hb.2⟩ ⟨hm.1,hm.2.2.1,hm.2.2.2⟩ loc hmem

theorem output_inclusion (c : CopyContract.Config) {l : Launch} {execution : Candidate}
    {sources : ReadsFrom} {order : Coherence} {o : Observation} {m : Machine}
    (hp : Pre c l) (hw : execution.WellFormed code l)
    (hc : GenericMemoryConditions execution l.initial sources order)
    (ho : ObserverConditions execution l.initial sources order o) (hd : o.domain = domain c)
    (hpre : CopyContract.Pre c m) :
    ∃ actions m', run code actions m = .ok m' ∧
      m'.threads.all (fun t => t.status == .done) = true ∧ CopyContract.Post c m' ∧
      ∀ loc ∈ domain c, o.output loc = Cells.encode m'.globalMem l.initial loc := by
  obtain ⟨m',hs,hdone,hpost⟩ := CopyCompletion.complete_from_pre hpre
  obtain ⟨actions,hrun⟩ := Termination.steps_run hs
  exact ⟨actions,m',hrun,hdone,hpost,domain_post_encoding_agreement c hp.2.2.2
    (Event.triple_apply (correct c) hp hw hc ho hd) hpost⟩

/-- Explicit host skip/no-launch bridge. This does NOT construct a zero-sized
physical launch: no PTX instructions execute and the initial byte map is returned.
The same original operational Pre/Config, including arbitrary frame data, applies. -/
theorem zero_count_skip (c : CopyContract.Config) {m : Machine} {initial : ByteMap}
    (hz : c.count = 0) (hp : CopyContract.Pre c m) (hi : Cells.Represents c.before initial) :
    c.n = 0 ∧ run code [] m = .ok m ∧
      m.threads.all (fun t => t.status == .done) = true ∧ CopyContract.Post c m ∧
      Cells.encode m.globalMem initial = initial ∧ ∀ l, ¬ Pre c l := by
  have hn : c.n = 0 := by have := c.coverage; omega
  have hthreads : m.threads = [] := List.eq_nil_iff_length_eq_zero.mpr (hp.count.trans hz)
  have hd : m.threads.all (fun t => t.status == .done) = true := by simp [hthreads]
  refine ⟨hn,rfl,hd,CopyContract.correct c m m hp (.refl m) hd,?_,?_⟩
  · rw [hp.memory]
    exact Cells.encode_of_representation hi
  · intro l hpre
    have hpositive := hpre.1
    rw [hz] at hpositive
    omega

end Ptx.CopyEvent
