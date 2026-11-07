import Ptx.Kernels.HopperDoubleBufferControlGenerations

/-! Actual CTA rendezvous source IDs and generation-indexed local cases.
No matching CTA participant, rank or convergence premise is assumed. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def ctaOffset (arrival : Bool) : Nat := if arrival then 0 else 1
def initialCtaId (tiles : Nat) (lane : Wgmma.Lane) (arrival : Bool) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,(if HopperStage.leader lane then 3 else 0)+ctaOffset arrival⟩
def reuseCtaId (a : TileA) (b : TileB) (tiles tile : Nat) (lane : Wgmma.Lane) (arrival : Bool) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,dataTileStart a b tiles tile lane+dataPreludeLength tiles tile lane+5+ctaOffset arrival⟩
def returnCtaId (a : TileA) (b : TileB) (tiles : Nat) (lane : Wgmma.Lane) (arrival : Bool) : Ptx.Event.EventId :=
  ⟨(ctx tiles lane).id,(dataPreOutputEvents a b tiles lane).length+4+ctaOffset arrival⟩

def sourceCtaTag (arrival : Bool) (event : Wgmma.Event) : Option (Nat × Nat) :=
  match Unified.eventView event with
  | .ampere (.ordinary (.barrierArrival bid generation)) => if arrival then some (bid,generation) else none
  | .ampere (.ordinary (.barrierReturn bid generation)) => if arrival then none else some (bid,generation)
  | _ => none

inductive CtaSource (a : TileA) (b : TileB) (tiles : Nat) : Ptx.Event.EventId → Bool → (Nat × Nat) → Prop
  | initial (lane : Wgmma.Lane) (arrival : Bool) : CtaSource a b tiles (initialCtaId tiles lane arrival) arrival (0,0)
  | reuse (tile : Nat) (lane : Wgmma.Lane) (arrival : Bool) (ht : tile < tiles) :
      CtaSource a b tiles (reuseCtaId a b tiles tile lane arrival) arrival (2,tile)
  | output (lane : Wgmma.Lane) (arrival : Bool) : CtaSource a b tiles (returnCtaId a b tiles lane arrival) arrival (1,0)

theorem data_initial_cta_case (a b tiles lane) (index : Nat) (event : Wgmma.Event) (arrival : Bool) (tag : Nat × Nat)
    (he : (dataInitialEvents a b tiles lane)[index]? = some event) (htag : sourceCtaTag arrival event = some tag) :
    CtaSource a b tiles ⟨(ctx tiles lane).id,index⟩ arrival tag := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  rw [data_initial_length] at hi
  cases hl : HopperStage.leader lane
  · have hb : index < 2 := by simpa only [hl,Bool.false_eq_true,ite_false] using hi
    interval_cases index
    all_goals simp only [dataInitialEvents,hl,initializationEvents,dataInitialCopies,Bool.false_eq_true,ite_false,
      List.nil_append,List.append_nil,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    all_goals cases he
    all_goals cases arrival <;> simp only [sourceCtaTag,Unified.eventView,Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,reduceCtorEq] at htag
    all_goals cases htag
    all_goals first
      | simpa only [initialCtaId,hl,ctaOffset,ite_true,ite_false,Bool.false_eq_true] using CtaSource.initial (a := a) (b := b) lane false
      | simpa only [initialCtaId,hl,ctaOffset,ite_true,ite_false,Bool.false_eq_true] using CtaSource.initial (a := a) (b := b) lane true
  · have hz : lane = 0 := (leader_iff_zero lane).mp hl
    subst lane
    have hb : index < 8 := hi
    interval_cases index
    all_goals cases he
    all_goals cases arrival <;> simp only [sourceCtaTag,Unified.eventView,Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,reduceCtorEq] at htag
    all_goals cases htag
    all_goals first
      | exact CtaSource.initial 0 false
      | exact CtaSource.initial 0 true

theorem data_initialization_cta_case (a b tiles lane) (index : Nat) (event : Wgmma.Event) (arrival : Bool) (tag : Nat × Nat)
    (he : (initializationEvents (HopperStage.leader lane))[index]? = some event) (htag : sourceCtaTag arrival event = some tag) :
    CtaSource a b tiles ⟨(ctx tiles lane).id,index⟩ arrival tag := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  apply data_initial_cta_case a b tiles lane index event arrival tag _ htag
  rw [dataInitialEvents,List.getElem?_append_left hi]
  exact he

theorem data_iteration_cta_case (a b tiles tile lane) (ht : tile < tiles)
    (index : Nat) (event : Wgmma.Event) (arrival : Bool) (tag : Nat × Nat)
    (he : (dataIterationEvents a b tiles tile lane)[index]? = some event) (htag : sourceCtaTag arrival event = some tag) :
    CtaSource a b tiles ⟨(ctx tiles lane).id,dataTileStart a b tiles tile lane+index⟩ arrival tag := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  rw [data_iteration_length] at hi
  by_cases hn : needsPrefetch tile tiles (HopperStage.leader lane)
  · have hb : index < 10 := by simpa only [dataPreludeLength,ite_eq_left hn] using hi
    interval_cases index
    all_goals simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,preludeEvents,ite_eq_left hn,
      prefetchTransferEvents,computeEvents,advanceEvents,data_prepared_generation_two,List.cons_append,List.nil_append,
      List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    all_goals cases he
    all_goals cases arrival <;> simp only [sourceCtaTag,Unified.eventView,Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,reduceCtorEq] at htag
    all_goals cases htag
    all_goals first
      | simpa only [reuseCtaId,dataPreludeLength,hn,ite_true,ctaOffset,Bool.false_eq_true,ite_false,Nat.add_zero] using CtaSource.reuse (a := a) (b := b) tile lane false ht
      | simpa only [reuseCtaId,dataPreludeLength,hn,ite_true,ctaOffset,Bool.false_eq_true,ite_false,Nat.add_zero] using CtaSource.reuse (a := a) (b := b) tile lane true ht
  · have hb : index < 7 := by simpa only [dataPreludeLength,ite_eq_right hn] using hi
    interval_cases index
    all_goals simp only [dataIterationEvents,iterationEvents,List.replicate_zero,List.nil_append,preludeEvents,ite_eq_right hn,
      computeEvents,advanceEvents,data_prepared_generation_two,List.cons_append,List.nil_append,
      List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    all_goals cases he
    all_goals cases arrival <;> simp only [sourceCtaTag,Unified.eventView,Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,reduceCtorEq] at htag
    all_goals cases htag
    all_goals first
      | simpa only [reuseCtaId,dataPreludeLength,hn,ite_false,ctaOffset,Bool.false_eq_true,ite_true,Nat.add_zero] using CtaSource.reuse (a := a) (b := b) tile lane false ht
      | simpa only [reuseCtaId,dataPreludeLength,hn,ite_false,ctaOffset,Bool.false_eq_true,ite_true,Nat.add_zero] using CtaSource.reuse (a := a) (b := b) tile lane true ht

theorem data_output_cta_case (a b tiles lane) (index : Nat) (event : Wgmma.Event) (arrival : Bool) (tag : Nat × Nat)
    (he : (outputEvents (ctx tiles lane) (dataPreOutputState a b tiles lane) lane (HopperStage.leader lane)
      (fun slot => result a b tiles (Wgmma.cCoord (lane,slot))))[index]? = some event)
    (htag : sourceCtaTag arrival event = some tag) :
    CtaSource a b tiles ⟨(ctx tiles lane).id,(dataPreOutputEvents a b tiles lane).length+index⟩ arrival tag := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  cases hl : HopperStage.leader lane
  · have hb : index < 6 := by simpa only [outputEvents,returnEvents,hl,Bool.false_eq_true,ite_false,
        List.length_append,outputWriteEvents,List.length_cons,List.length_nil] using hi
    interval_cases index
    all_goals simp only [outputEvents,returnEvents,hl,Bool.false_eq_true,ite_false,outputWriteEvents,data_return_generation_one,
      List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    all_goals cases he
    all_goals cases arrival <;> simp only [sourceCtaTag,Unified.eventView,Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,reduceCtorEq] at htag
    all_goals cases htag
    all_goals first
      | simpa only [returnCtaId,ctaOffset,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using CtaSource.output (a := a) (b := b) lane false
      | simpa only [returnCtaId,ctaOffset,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using CtaSource.output (a := a) (b := b) lane true
  · have hz : lane = 0 := (leader_iff_zero lane).mp hl
    subst lane
    have hb : index < 8 := by simpa only [outputEvents,returnEvents,hl,ite_true,
        List.length_append,outputWriteEvents,List.length_cons,List.length_nil] using hi
    interval_cases index
    all_goals simp only [outputEvents,returnEvents,hl,ite_true,outputWriteEvents,data_return_generation_one,
      List.cons_append,List.nil_append,List.getElem?_cons_succ,List.getElem?_cons_zero] at he
    all_goals cases he
    all_goals cases arrival <;> simp only [sourceCtaTag,Unified.eventView,Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,reduceCtorEq] at htag
    all_goals cases htag
    all_goals first
      | simpa only [returnCtaId,ctaOffset,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using CtaSource.output (a := a) (b := b) 0 false
      | simpa only [returnCtaId,ctaOffset,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using CtaSource.output (a := a) (b := b) 0 true

end
end Ptx.Kernels.HopperDoubleBuffer
