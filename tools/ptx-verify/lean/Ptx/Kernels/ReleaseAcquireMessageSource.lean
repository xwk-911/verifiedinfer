import Ptx.Ordered.Memory
import Ptx.Generated.ReleaseAcquireMessage
import Ptx.Scalar.IntegerMemory

/-! Actual source and event structure of the mechanically generated two-thread
message-passing fixture. This file supplies local provenance, including a finite
poll retry. Memory consistency and universal observer contracts are separate. -/
namespace Ptx.Kernels.ReleaseAcquireMessage
open Ptx.ISA Ptx.Ordered
noncomputable section

def code := Generated.release_acquire_message.program
def block : Dim3 := ⟨2,1,1⟩
def id (tid : Nat) : ThreadId := ⟨.zero,⟨tid,0,0⟩⟩
def bindings : Bindings := [("DATA",64),("FLAG",128),("OUT",256)]
def context (tid : Nat) : Scalar.Context := {id := id tid,block := block,params := bindings}
def oracle : Ordered.Oracle := fun query => .integer (if query = 0 then 1 else 42)
def result (tid count : Nat) : Ordered.State × List Ordered.Kind :=
  (Ordered.run (context tid) oracle code count {}).toOption.getD ({},[])
def trace (tid count : Nat) : Ordered.ThreadTrace :=
  ⟨id tid,oracle,count,(result tid count).1,(result tid count).2⟩
def candidate : Ordered.Candidate := ⟨[trace 0 9,trace 1 12]⟩
def launch : Scalar.Launch := ⟨⟨.one,block⟩,bindings,fun _ => .bits (byte 0)⟩

theorem mechanically_typed : Ordered.ProgramTyped 70 Generated.release_acquire_message.registerDeclarations
    Generated.release_acquire_message.parameters code := Generated.release_acquire_message.checked.valid

theorem producer_source_run : Ordered.Produced code bindings block (trace 0 9) := rfl
theorem consumer_source_run : Ordered.Produced code bindings block (trace 1 12) := rfl
theorem source_candidate_is_complete : Ordered.Complete candidate := by
  intro actual ht
  simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl <;> rfl

theorem source_candidate_is_well_formed : Ordered.WellFormed code launch candidate := by
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [launch,block,Geometry.Valid,Dim3.Positive,Dim3.one]
  · change ([id 0,id 1].Nodup)
    decide
  · intro actual ht
    simp only [candidate,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨by norm_num [trace,id,launch,block,ThreadId.Valid,Dim3.Within,Dim3.zero,Dim3.one],producer_source_run⟩
    · exact ⟨by norm_num [trace,id,launch,block,ThreadId.Valid,Dim3.Within,Dim3.zero,Dim3.one],consumer_source_run⟩
  · rintro ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩ hi
    simp only [ThreadId.Valid,Dim3.Within,launch,block,Dim3.one] at hi
    have hz : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ ty = 0 ∧ tz = 0 := by omega
    obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := hz
    have hx : tx = 0 ∨ tx = 1 := by omega
    rcases hx with rfl | rfl
    · exact ⟨trace 0 9,by simp [candidate],rfl⟩
    · exact ⟨trace 1 12,by simp [candidate],rfl⟩

theorem actual_producer_order_and_scope : ((trace 0 9).events.map fun kind => (kind.order,kind.scope)) =
    [(.weak,none),(.release,some .gpu)] := rfl
theorem actual_consumer_order_and_scope : ((trace 1 12).events.map fun kind => (kind.order,kind.scope)) =
    [(.acquire,some .gpu),(.weak,none),(.weak,none)] := rfl

theorem source_oracle_queries_are_preserved : (trace 0 9).final.core.queries = 0 ∧
    (trace 1 12).final.core.queries = 2 := ⟨rfl,rfl⟩

def retryOracle : Ordered.Oracle := fun query => .integer (if query = 0 then 0 else if query = 1 then 1 else 42)
def retryResult : Ordered.State × List Ordered.Kind :=
  (Ordered.run (context 1) retryOracle code 15 {}).toOption.getD ({},[])
def retryTrace : Ordered.ThreadTrace := ⟨id 1,retryOracle,15,retryResult.1,retryResult.2⟩
theorem polling_retry_is_an_actual_source_run : Ordered.Produced code bindings block retryTrace := rfl
theorem polling_retry_retains_both_acquires : (retryTrace.events.map fun kind => kind.order) =
    [.acquire,.acquire,.weak,.weak] := rfl
theorem polling_retry_consumes_three_queries : retryTrace.final.core.queries = 3 := rfl

theorem ordered_integer_load_rejects_a_real_oracle_reply :
    (Ordered.run (context 1) (fun _ => .real .f32 0)
      [.load .acquire .gpu "%seen" ⟨.imm 64,0⟩] 1 {}).toOption.isNone = true := rfl

def payloadWrite : Ptx.Event.EventId := ⟨id 0,0⟩
def flagWrite : Ptx.Event.EventId := ⟨id 0,1⟩
def flagRead : Ptx.Event.EventId := ⟨id 1,0⟩
def payloadRead : Ptx.Event.EventId := ⟨id 1,1⟩
def flag : Location := ⟨.global,128⟩
def payload : Location := ⟨.global,64⟩
def rf : Ptx.Event.ReadsFrom := fun read _ =>
  if read = flagRead then .write flagWrite else if read = payloadRead then .write payloadWrite else .initial

theorem flag_endpoints_are_mutually_strong : Ordered.MorallyStrong candidate flagWrite flagRead := by
  refine ⟨Or.inr ⟨.gpu,.gpu,rfl,rfl,True.intro,True.intro⟩,?_⟩
  exact ⟨(flag,4),rfl,rfl⟩

theorem flag_read_observes_release : Ordered.Observed candidate rf flagWrite flagRead := by
  exact ⟨flag_endpoints_are_mutually_strong,flag,Scalar.u32Byte 1 0,rfl,rfl,rfl⟩

theorem direct_release_acquire_synchronizes : Ordered.ReleaseAcquireSync candidate rf flagWrite flagRead :=
  ⟨rfl,rfl,flag_endpoints_are_mutually_strong,.direct flag_read_observes_release⟩

theorem producer_payload_precedes_release : Ptx.Event.ProgramOrder candidate.view payloadWrite flagWrite :=
  ⟨rfl,rfl,rfl,by decide⟩
theorem consumer_acquire_precedes_payload : Ptx.Event.ProgramOrder candidate.view flagRead payloadRead :=
  ⟨rfl,rfl,rfl,by decide⟩

theorem payload_publication_is_causal : Ordered.BaseCausality candidate rf payloadWrite payloadRead :=
  Ordered.publish_release_acquire producer_payload_precedes_release direct_release_acquire_synchronizes
    consumer_acquire_precedes_payload

end
end Ptx.Kernels.ReleaseAcquireMessage
