import Ptx.Kernels.CpAsyncCopySpec
import Ptx.Kernels.CpAsyncCopyMemory

/-! All-candidate output/frame correctness against an independent byte spec.
Eligibility is derived from the actual graph and disjoint layout, not a caller
premise. Independent complete consistency/observer existence remains separate.
-/
namespace Ptx.CpAsyncCopyGraph
open Ptx.ISA Ptx.Ampere Ptx.CpAsyncCopyTrace
noncomputable section

theorem graph_correct {cfg : CpAsyncCopySpec.Config} {bytes answers initial rf co o}
    (hl : CpAsyncCopySpec.Layout cfg)
    (hm : MemoryConstraints (graph cfg.src cfg.dst bytes answers) initial rf co)
    (ho : ObserverConstraints (graph cfg.src cfg.dst bytes answers) initial rf co o)
    (hsize : bytes.length = 16) (hdomain : o.domain = CpAsyncCopySpec.domain cfg) :
    CpAsyncCopySpec.Post cfg initial o.output := by
  have hdisjoint : cfg.src+16 ≤ cfg.dst ∨ cfg.dst+16 ≤ cfg.src := hl.2.2.2.2.2
  have hfree := race_free (answers := answers) hsize hdisjoint rf
  constructor
  · intro offset hoff
    let i : Fin 4 := ⟨offset/4,by omega⟩
    have hrem : offset % 4 < 4 := Nat.mod_lt _ (by decide)
    have hindex : 4*i.val+offset%4 = offset := by dsimp [i]; omega
    have hd : (⟨.global,cfg.dst+4*i.val+offset%4⟩ : Location) ∈ o.domain := by
      rw [hdomain]
      simpa only [Nat.add_assoc,hindex] using CpAsyncCopySpec.output_in_domain hl offset hoff
    have hv := observed_output_byte hm ho hsize hdisjoint i (offset%4) hrem hd
    simpa only [Nat.add_assoc,hindex] using hv
  · intro loc hmem hframe
    have hglobal := CpAsyncCopySpec.domain_global hmem
    apply MemoryGraph.observer_unwritten ho (hdomain ▸ hmem)
      (MemoryGraph.race_free_observer_eligible hfree _)
    intro writer
    rw [graph_writeByte]
    cases hw : (graph cfg.src cfg.dst bytes answers).writeByte writer loc with
    | none => rfl
    | some value =>
      rcases write_cases hw with ⟨_,hp⟩ | ⟨i,_,hp⟩
      · have hb := Ptx.Event.payloadByte_bounds hp
        rw [hglobal] at hb
        cases hb.1
      · have hb := Ptx.Event.payloadByte_bounds hp
        simp only [Scalar.u32_bytes_size] at hb
        have := i.isLt
        exact (hframe ⟨hglobal,by omega,by omega⟩).elim

def Pre (cfg : CpAsyncCopySpec.Config) (l : Scalar.Launch) : Prop :=
  CpAsyncCopySpec.Layout cfg ∧ CpAsyncCopySpec.Input cfg l.initial ∧ l = launch cfg.src cfg.dst l.initial

theorem correct (cfg : CpAsyncCopySpec.Config) : CheckedTriple code (Pre cfg)
    (fun _ => CpAsyncCopySpec.domain cfg) (fun l output => CpAsyncCopySpec.Post cfg l.initial output) := by
  intro l c rf co o hp hm ho hdomain
  have hsrc : cfg.src < 2^64 := by
    obtain ⟨ha,hs,_,_⟩ := hp.1
    omega
  have hdst : cfg.dst+16 ≤ 2^64 := by
    obtain ⟨ha,_,hd,_⟩ := hp.1
    omega
  have hw : WellFormed code (launch cfg.src cfg.dst l.initial) c := by
    rw [← hp.2.2]
    exact hm.provenance
  obtain ⟨bytes,answers,hsize,hview⟩ := candidate_view hsrc hdst hw ho.complete
  have hmem := hm.memory
  change MemoryGraph.MemoryConditions c.memoryGraph l.initial rf co at hmem
  rw [hview] at hmem
  have hob := ho
  change MemoryGraph.ObserverConditions c.memoryGraph l.initial rf co o at hob
  rw [hview] at hob
  exact graph_correct hp.1 hmem hob hsize hdomain

end
end Ptx.CpAsyncCopyGraph
