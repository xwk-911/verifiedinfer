import Ptx.Tests.MmaLocal

/-! A graph-level negative checks control rendezvous without granting memory
publication. The synthetic graph is not claimed to be a source witness. -/
namespace Ptx.MmaControlTests
open Ptx.ISA Ptx.Ampere
noncomputable section

def left : ThreadId := ⟨.zero,.zero⟩
def right : ThreadId := ⟨.zero,⟨1,0,0⟩⟩
def call : MmaCall := MmaLocalTests.fallback
def trace (thread : ThreadId) (events : List Event) : ThreadTrace :=
  ⟨thread,MmaLocalTests.oracle,0,{},events⟩
def candidate : Candidate := ⟨[
  trace left [.mmaEntry call,.mmaReturn call,.ordinary (.barrierArrival 0 0),.ordinary (.barrierReturn 0 0)],
  trace right [.ordinary (.barrierArrival 0 0),.ordinary (.barrierReturn 0 0),.mmaEntry call,.mmaReturn call]]⟩
def event (thread : ThreadId) (serial : Nat) : Node := .thread ⟨thread,serial⟩

theorem left_order : ProgramOrder candidate (event left 1) (event left 2) := ⟨rfl,rfl,rfl,by decide⟩
theorem barrier_order : BarrierSync candidate (event left 2) (event right 1) := ⟨rfl,0,0,rfl,rfl⟩
theorem right_order : ProgramOrder candidate (event right 1) (event right 2) := ⟨rfl,rfl,rfl,by decide⟩
theorem rendezvous : MmaControl candidate (event right 2) (event left 1) := ⟨rfl,call,call,rfl,rfl,rfl,rfl,rfl⟩

theorem circular_control_rejected : ¬ ControlAcyclic candidate := by
  intro hc
  have p1 : Ptx.Event.Path (ControlEdge candidate) (event left 1) (event left 2) := .single (.inl (.inl left_order))
  have p2 : Ptx.Event.Path (ControlEdge candidate) (event left 2) (event right 1) := .single (.inl (.inr (.inl barrier_order)))
  have p3 : Ptx.Event.Path (ControlEdge candidate) (event right 1) (event right 2) := .single (.inl (.inl right_order))
  have p4 : Ptx.Event.Path (ControlEdge candidate) (event right 2) (event left 1) := .single (.inr (.inr rendezvous))
  exact hc (event left 1) (.trans p1 (.trans p2 (.trans p3 p4)))

theorem rendezvous_not_memory_base_edge : ¬ BaseEdge candidate (event right 2) (event left 1) := by
  simp [BaseEdge,ProgramOrder,BarrierSync,IssueBefore,CopyInternal,Completion,event,
    Candidate.eventAt,Candidate.traceAt,candidate,trace,left,right]

end
end Ptx.MmaControlTests
