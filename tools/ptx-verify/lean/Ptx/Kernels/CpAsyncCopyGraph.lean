import Ptx.Kernels.CpAsyncCopySource
import Ptx.Ampere.Checked

/-! Actual source-produced singleton candidate family. Payload and scalar answers
are independent parameters. Neither this family nor source reconstruction fixes
the permitted rf/co witnesses or the initial input bytes. -/
namespace Ptx.CpAsyncCopyGraph
open Ptx.ISA Ptx.Ampere
open Ptx.CpAsyncCopyTrace
noncomputable section

def thread : ThreadId := ⟨.zero,.zero⟩
def oracle (bytes : List Symbolic.Byte) (answers : Answers) : Ampere.Oracle := {
  bytes := fun _ => bytes
  scalar := fun q => .integer (if q = 1 then answers 0 else if q = 2 then answers 1 else if q = 3 then answers 2 else answers 3)
}
def trace (src dst : Nat) (bytes : List Symbolic.Byte) (answers : Answers) : ThreadTrace :=
  ⟨thread,oracle bytes answers,15,finalState thread src dst bytes answers,events thread src dst bytes answers⟩
def graph (src dst : Nat) (bytes : List Symbolic.Byte) (answers : Answers) : Candidate :=
  ⟨[trace src dst bytes answers]⟩
def launch (src dst : Nat) (initial : Ptx.Event.ByteMap Symbolic.Byte) : Scalar.Launch :=
  ⟨⟨.one,.one⟩,[("X",src),("Y",dst)],initial⟩

theorem produced (src dst : Nat) (bytes : List Symbolic.Byte) (answers : Answers)
    (hs : src < 2^64) (hd : dst+16 ≤ 2^64) (hb : bytes.length = 16) :
    Ampere.Produced code [("X",src),("Y",dst)] .one (trace src dst bytes answers) := by
  apply translated_run (ctx := {id := thread,params := [("X",src),("Y",dst)],block := .one})
    (oracle bytes answers) src dst answers rfl rfl hs hd hb
  intro i
  fin_cases i <;> rfl

theorem valid_thread_unique {id : ThreadId} (hv : id.Valid (⟨.one,.one⟩ : Geometry)) : id = thread := by
  rcases id with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
  simp only [ThreadId.Valid,Dim3.Within,Dim3.one] at hv
  have hh : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ tx = 0 ∧ ty = 0 ∧ tz = 0 := by omega
  rcases hh with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  rfl

theorem wellFormed (src dst : Nat) (bytes : List Symbolic.Byte) (answers : Answers)
    (initial : Ptx.Event.ByteMap Symbolic.Byte)
    (hs : src < 2^64) (hd : dst+16 ≤ 2^64) (hb : bytes.length = 16) :
    WellFormed code (launch src dst initial) (graph src dst bytes answers) := by
  refine ⟨by norm_num [launch,Geometry.Valid,Dim3.Positive,Dim3.one],by simp [graph],?_,?_⟩
  · intro t ht
    have he : t = trace src dst bytes answers := List.mem_singleton.mp ht
    subst t
    exact ⟨by norm_num [trace,thread,launch,ThreadId.Valid,Dim3.Within,Dim3.one,Dim3.zero],produced src dst bytes answers hs hd hb⟩
  · intro id hv
    exact ⟨trace src dst bytes answers,List.mem_singleton_self _,(valid_thread_unique hv).symm⟩

theorem complete (src dst : Nat) (bytes : List Symbolic.Byte) (answers : Answers) :
    Complete (graph src dst bytes answers) := by
  intro t ht
  have he : t = trace src dst bytes answers := List.mem_singleton.mp ht
  subst t
  rfl

theorem eventAt (src dst : Nat) (bytes : List Symbolic.Byte) (answers : Answers) (event : Ptx.Event.EventId) :
    (graph src dst bytes answers).eventAt event =
      if event.thread = thread then (events thread src dst bytes answers)[event.serial]? else none := by
  by_cases he : event.thread = thread
  · simp [Candidate.eventAt,Candidate.traceAt,graph,trace,he]
  · simp [Candidate.eventAt,Candidate.traceAt,graph,trace,he,beq_iff_eq,Ne.symm he]
theorem copyAt (src dst : Nat) (bytes : List Symbolic.Byte) (answers : Answers) (id : CopyId) :
    (graph src dst bytes answers).copyAt id =
      if id.thread = thread ∧ id.ordinal = 0 then some (operation thread src bytes) else none := by
  by_cases he : id.thread = thread
  · cases id with
    | mk owner ordinal =>
      dsimp only at he
      subst owner
      cases ordinal <;> simp [Candidate.copyAt,Candidate.traceAt,graph,trace,finalState,beforeRet]
  · simp [Candidate.copyAt,Candidate.traceAt,graph,trace,he,beq_iff_eq,Ne.symm he]

theorem single_trace {src dst initial c} (hw : WellFormed code (launch src dst initial) c) :
    ∃ t, c.traces = [t] ∧ t.id = thread := by
  have valid : ∀ t ∈ c.traces, t.id = thread := fun t ht => valid_thread_unique (hw.2.2.1 t ht).1
  obtain ⟨t,ht,_⟩ := hw.2.2.2 thread (by norm_num [launch,thread,ThreadId.Valid,Dim3.Within,Dim3.zero,Dim3.one])
  cases hcs : c.traces with
  | nil => simp [hcs] at ht
  | cons first rest =>
    have hf := valid first (by simp [hcs])
    cases rest with
    | nil => exact ⟨first,rfl,hf⟩
    | cons second rest =>
      have hs := valid second (by simp [hcs])
      have hn := hw.2.1
      rw [hcs] at hn
      simp only [List.map_cons,List.nodup_cons,List.mem_cons] at hn
      exact (hn.1 (.inl (hf.trans hs.symm))).elim

/-- Every completed source candidate has this augmented memory view. Oracle
metadata and unused replies need not equal the selected representative oracle. -/
theorem candidate_view {src dst initial c}
    (hs : src < 2^64) (hd : dst+16 ≤ 2^64)
    (hw : WellFormed code (launch src dst initial) c) (hc : Complete c) :
    ∃ bytes answers, bytes.length = 16 ∧ c.memoryGraph = (graph src dst bytes answers).memoryGraph := by
  obtain ⟨t,hcs,hid⟩ := single_trace hw
  have ht : t ∈ c.traces := by simp [hcs]
  have hp := (hw.2.2.1 t ht).2
  obtain ⟨answers,hb,_,_,hfinal,hevents⟩ := complete_source_shape
    (ctx := {id := t.id,params := [("X",src),("Y",dst)],block := .one}) rfl rfl hs hd hp (hc t ht)
  refine ⟨t.oracle.bytes 0,answers,hb,memoryGraph_eq ?_ ?_ ?_⟩
  · funext ev
    rw [eventAt]
    by_cases he : ev.thread = thread
    · simp [Candidate.eventAt,Candidate.traceAt,hcs,hid,he,hevents]
    · simp [Candidate.eventAt,Candidate.traceAt,hcs,hid,he,hevents,beq_iff_eq,Ne.symm he]
  · funext op
    rw [copyAt]
    by_cases he : op.thread = thread
    · cases op with
      | mk owner ordinal =>
        dsimp only at he
        subst owner
        cases ordinal <;>
          simp [Candidate.copyAt,Candidate.traceAt,hcs,hid,hfinal,finalState,beforeRet]
    · simp [Candidate.copyAt,Candidate.traceAt,hcs,hid,he,beq_iff_eq,Ne.symm he]
  · exact ⟨fun _ => complete src dst (t.oracle.bytes 0) answers,fun _ => hc⟩

end
end Ptx.CpAsyncCopyGraph
