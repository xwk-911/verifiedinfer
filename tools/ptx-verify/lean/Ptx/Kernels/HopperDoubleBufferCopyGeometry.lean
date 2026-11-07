import Ptx.Kernels.HopperDoubleBufferCandidateMemory

/-! Source-derived geometry of every actual TMA issue, independent of captured
descriptor/payload/matrix replies and lane-specific finite retry schedules.
No resource history, memory values or arithmetic result is assumed here. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def CopyAAt (copy : TmaCopy) (tile : Nat) : Prop :=
  copy.descriptorAddress = 4096 ∧ copy.coordinates = ⟨0,(8*tile : Nat)⟩ ∧
    copy.destination = aBase (stage tile) ∧ copy.barrier = barrierAddress (stage tile)
def CopyBAt (copy : TmaCopy) (tile : Nat) : Prop :=
  copy.descriptorAddress = 4224 ∧ copy.coordinates = ⟨0,(tile : Int)⟩ ∧
    copy.destination = bBase (stage tile) ∧ copy.barrier = barrierAddress (stage tile)
def CopyGeometry (tiles : Nat) (copy : TmaCopy) : Prop :=
  ∃ tile < tiles, CopyAAt copy tile ∨ CopyBAt copy tile

theorem initialization_no_tma_issue (leader : Bool) (copy : TmaCopy) :
    Wgmma.Event.base (.tmaIssue copy) ∉ initializationEvents leader := by
  cases leader <;> simp [initializationEvents]

theorem output_no_tma_issue (context s lane leader values) (copy : TmaCopy) :
    Wgmma.Event.base (.tmaIssue copy) ∉ outputEvents context s lane leader values := by
  cases leader <;> simp [outputEvents,outputWriteEvents,outputWriteEvent,returnEvents]

theorem reply_initial_copy_geometry {tiles reply leader copy} (ht : 0 < tiles)
    (hm : Wgmma.Event.base (.tmaIssue copy) ∈ replyInitialCopies reply leader) : CopyGeometry tiles copy := by
  cases leader with
  | false => simp [replyInitialCopies] at hm
  | true =>
    simp only [replyInitialCopies,ite_true,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with h | h | h
    · cases h
    · cases h; exact ⟨0,ht,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩
    · cases h; exact ⟨0,ht,Or.inr ⟨rfl,rfl,rfl,rfl⟩⟩

theorem prelude_copy_geometry {context reply s tile tiles leader copy} (hb : tiles ≤ 2^28)
    (hm : Wgmma.Event.base (.tmaIssue copy) ∈ preludeEvents context reply s tile tiles leader 4096 4224) :
    CopyGeometry tiles copy := by
  by_cases hn : needsPrefetch tile tiles leader
  · have hcoord := source_coordinate_small hn.1 hb
    simp only [preludeEvents,ite_eq_left hn,prefetchTransferEvents,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with h | h | h
    · cases h
    · cases h
      exact ⟨tile+1,hn.1,Or.inl ⟨rfl,by simp only [prefetchACopy,hcoord.2.1],rfl,rfl⟩⟩
    · cases h
      exact ⟨tile+1,hn.1,Or.inr ⟨rfl,by simp only [prefetchBCopy,hcoord.2.2],rfl,rfl⟩⟩
  · simp only [preludeEvents,ite_eq_right hn,List.not_mem_nil] at hm

theorem iteration_copy_geometry {context reply s tile tiles retries leader values copy} (hb : tiles ≤ 2^28)
    (hm : Wgmma.Event.base (.tmaIssue copy) ∈ iterationEvents context reply s tile tiles retries leader 4096 4224 values) :
    CopyGeometry tiles copy := by
  simp [iterationEvents,waitEvent,computeEvents,advanceEvents] at hm
  exact prelude_copy_geometry hb hm

theorem loop_copy_geometry {context reply first tiles leader retries s values n copy} (hb : tiles ≤ 2^28)
    (hm : Wgmma.Event.base (.tmaIssue copy) ∈ loopEvents context reply first tiles leader retries s values 4096 4224 n) :
    CopyGeometry tiles copy := by
  induction n with
  | zero => cases hm
  | succ n ih =>
    rw [loopEvents,List.mem_append] at hm
    exact hm.elim ih (iteration_copy_geometry hb)

theorem positive_copy_geometry {tiles lane reply retries copy} (ht : 0 < tiles) (hb : tiles ≤ 2^28)
    (hm : Wgmma.Event.base (.tmaIssue copy) ∈ replyPositiveEvents tiles lane reply retries) : CopyGeometry tiles copy := by
  simp only [replyPositiveEvents,List.mem_append] at hm
  rcases hm with (h | h) | h | h
  · exact (initialization_no_tma_issue _ _ h).elim
  · exact reply_initial_copy_geometry ht h
  · exact loop_copy_geometry hb h
  · exact (output_no_tma_issue _ _ _ _ _ _ h).elim

theorem zero_no_tma_issue (lane : Wgmma.Lane) (copy : TmaCopy) :
    Wgmma.Event.base (.tmaIssue copy) ∉ completeEvents 0 lane := by
  simp only [completeEvents,preOutputEvents,ite_true,List.mem_append]
  exact fun h => h.elim (initialization_no_tma_issue _ _) (output_no_tma_issue _ _ _ _ _ _)

theorem candidate_copy_geometry {tiles initial candidate id copy} (hb : tiles ≤ 2^28)
    (hw : Unified.WellFormed code (completeLaunch tiles initial) candidate) (hc : Unified.Complete candidate)
    (he : Tma.copyAt candidate.view id = some copy) : CopyGeometry tiles copy := by
  have hh := Unified.view_tma_iff.mp (Tma.copyAt_iff.mp he)
  obtain ⟨trace,ht,_,hget⟩ := Unified.eventAt_trace hh
  have hm := List.mem_of_getElem? hget
  obtain ⟨lane,_,hzero | hpositive⟩ := completed_candidate_trace_reconstruct hb hw hc ht
  · rw [hzero.2.2.2] at hm
    exact (zero_no_tma_issue lane copy hm).elim
  · obtain ⟨hpos,retries,_,_,hevents⟩ := hpositive
    rw [hevents] at hm
    exact positive_copy_geometry hpos hb hm

end
end Ptx.Kernels.HopperDoubleBuffer
