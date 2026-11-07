import Ptx.Kernels.ShufflePairAgreement
import Ptx.Shuffle.Source

/-! Reconstruction of every completed source trace of the generated pair
program. No canonical oracle, fixed trace order or supplied step count is
assumed. This closes the gap between a constructed family and all candidates. -/
namespace Ptx.Kernels.ShufflePair
open Ptx.ISA Ptx.Shuffle
noncomputable section

def Pre (launch : Scalar.Launch) : Prop := launch.geometry = ⟨.one,block⟩ ∧ launch.params = []

theorem valid_thread_is_lane {thread : ThreadId} (ht : thread.Valid ⟨.one,block⟩) : ∃ which : Lane2, thread = id which := by
  rcases thread with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
  simp only [ThreadId.Valid,Dim3.Within,Dim3.one,block] at ht
  have hcx : cx = 0 := by omega
  have hcy : cy = 0 := by omega
  have hcz : cz = 0 := by omega
  have hty : ty = 0 := by omega
  have htz : tz = 0 := by omega
  subst cx; subst cy; subst cz; subst ty; subst tz
  exact ⟨⟨tx,by omega⟩,rfl⟩

theorem arbitrary_oracle_source_run (which : Lane2) (answers : Shuffle.Oracle) (params : Bindings) :
    Shuffle.run {id := id which,params := params,block := block} answers Generated.shuffle_pair.program 3 {} =
      .ok (finalState which (answers.shuffle 0).1 (answers.shuffle 0).2,
        [.shuffle (record which (answers.shuffle 0).1 (answers.shuffle 0).2)]) := by
  fin_cases which <;> rfl

theorem completed_trace_shape {trace : Shuffle.ThreadTrace} (which : Lane2) (hi : trace.id = id which)
    (hp : Shuffle.Produced Generated.shuffle_pair.program [] block trace)
    (hd : trace.final.base.core.thread.status = .done) :
    trace.count = 3 ∧ trace.final = finalState which (trace.oracle.shuffle 0).1 (trace.oracle.shuffle 0).2 ∧
      trace.events = [.shuffle (record which (trace.oracle.shuffle 0).1 (trace.oracle.shuffle 0).2)] := by
  have hr := arbitrary_oracle_source_run which trace.oracle []
  unfold Shuffle.Produced at hp
  rw [hi] at hp
  exact Shuffle.complete_run_unique hp hd hr rfl

theorem member_source_shape {launch candidate trace} (hp : Pre launch)
    (hw : Shuffle.WellFormed Generated.shuffle_pair.program launch candidate) (hc : Shuffle.Complete candidate)
    (ht : trace ∈ candidate.traces) :
    ∃ which : Lane2, trace.id = id which ∧ trace.count = 3 ∧
      trace.final = finalState which (trace.oracle.shuffle 0).1 (trace.oracle.shuffle 0).2 ∧
      trace.events = [.shuffle (record which (trace.oracle.shuffle 0).1 (trace.oracle.shuffle 0).2)] := by
  have hi := (hw.2.2.1 trace ht).1
  rw [hp.1] at hi
  obtain ⟨which,hi⟩ := valid_thread_is_lane hi
  have hs := (hw.2.2.1 trace ht).2
  rw [hp.1,hp.2] at hs
  exact ⟨which,hi,completed_trace_shape which hi hs (hc trace ht)⟩

theorem actual_event_shape {launch candidate actual kind} (hp : Pre launch)
    (hw : Shuffle.WellFormed Generated.shuffle_pair.program launch candidate) (hc : Shuffle.Complete candidate)
    (he : candidate.eventAt actual = some kind) :
    ∃ which : Lane2, ∃ value predicate, actual = event which ∧ kind = .shuffle (record which value predicate) := by
  obtain ⟨trace,ht,hi,hget⟩ := Shuffle.eventAt_trace he
  obtain ⟨which,hid,_,_,hev⟩ := member_source_shape hp hw hc ht
  rw [hev] at hget
  have hn : actual.serial = 0 := by cases hs : actual.serial with
    | zero => rfl
    | succ serial => simp [hs] at hget
  refine ⟨which,(trace.oracle.shuffle 0).1,(trace.oracle.shuffle 0).2,?_,?_⟩
  · cases actual
    simp only at hn hi
    simp only [event,←hi,hid,hn]
  · simpa only [hn,List.getElem?_cons_zero,Option.some.injEq] using hget.symm

theorem actual_shuffle_shape {launch candidate actual result} (hp : Pre launch)
    (hw : Shuffle.WellFormed Generated.shuffle_pair.program launch candidate) (hc : Shuffle.Complete candidate)
    (he : candidate.shuffleAt actual = some result) :
    ∃ which : Lane2, ∃ value predicate, actual = event which ∧ result = record which value predicate := by
  obtain ⟨which,value,predicate,hi,hk⟩ := actual_event_shape hp hw hc (Shuffle.shuffleAt_eventAt he)
  exact ⟨which,value,predicate,hi,Shuffle.Kind.shuffle.inj hk⟩

theorem each_lane_arrives {launch candidate} (hp : Pre launch)
    (hw : Shuffle.WellFormed Generated.shuffle_pair.program launch candidate) (hc : Shuffle.Complete candidate) (which : Lane2) :
    ∃ value predicate, candidate.shuffleAt (event which) = some (record which value predicate) := by
  have hv : (id which).Valid launch.geometry := by
    rw [hp.1]
    fin_cases which <;> simp [ThreadId.Valid,Dim3.Within,Dim3.one,Dim3.zero,block,Ptx.Kernels.ShufflePair.id]
  obtain ⟨trace,ht,hi⟩ := hw.2.2.2 (id which) hv
  obtain ⟨_,_,hev⟩ := completed_trace_shape which hi (by
    have hs := (hw.2.2.1 trace ht).2
    simpa only [hp.1,hp.2] using hs) (hc trace ht)
  refine ⟨(trace.oracle.shuffle 0).1,(trace.oracle.shuffle 0).2,?_⟩
  unfold Shuffle.Candidate.shuffleAt
  rw [Shuffle.eventAt_of_member hw.2.1 ht (show (event which).thread = trace.id from hi.symm),hev]
  rfl

end
end Ptx.Kernels.ShufflePair
