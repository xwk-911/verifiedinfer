import Ptx.Kernels.ReleaseAcquireMessageSource

/-! Concrete source regressions plus deliberately constructed scope graphs.
The source fixture is shared with its production memory-witness proofs. -/
namespace Ptx.OrderedTests
open Ptx.ISA Ptx.Ordered
noncomputable section

abbrev code := Kernels.ReleaseAcquireMessage.code

abbrev block := Kernels.ReleaseAcquireMessage.block

abbrev id := Kernels.ReleaseAcquireMessage.id

abbrev bindings := Kernels.ReleaseAcquireMessage.bindings

abbrev context := Kernels.ReleaseAcquireMessage.context

abbrev oracle := Kernels.ReleaseAcquireMessage.oracle

abbrev result := Kernels.ReleaseAcquireMessage.result

abbrev trace := Kernels.ReleaseAcquireMessage.trace

abbrev candidate := Kernels.ReleaseAcquireMessage.candidate

abbrev launch := Kernels.ReleaseAcquireMessage.launch

theorem mechanically_typed : Ordered.ProgramTyped 70 Generated.release_acquire_message.registerDeclarations
    Generated.release_acquire_message.parameters code := Kernels.ReleaseAcquireMessage.mechanically_typed

theorem producer_source_run : Ordered.Produced code bindings block (trace 0 9) := Kernels.ReleaseAcquireMessage.producer_source_run

theorem consumer_source_run : Ordered.Produced code bindings block (trace 1 12) := Kernels.ReleaseAcquireMessage.consumer_source_run

theorem source_candidate_is_complete : Ordered.Complete candidate := Kernels.ReleaseAcquireMessage.source_candidate_is_complete

theorem source_candidate_is_well_formed : Ordered.WellFormed code launch candidate := Kernels.ReleaseAcquireMessage.source_candidate_is_well_formed

theorem actual_producer_order_and_scope : ((trace 0 9).events.map fun kind => (kind.order,kind.scope)) =
    [(.weak,none),(.release,some .gpu)] := Kernels.ReleaseAcquireMessage.actual_producer_order_and_scope

theorem actual_consumer_order_and_scope : ((trace 1 12).events.map fun kind => (kind.order,kind.scope)) =
    [(.acquire,some .gpu),(.weak,none),(.weak,none)] := Kernels.ReleaseAcquireMessage.actual_consumer_order_and_scope

theorem source_oracle_queries_are_preserved : (trace 0 9).final.core.queries = 0 ∧
    (trace 1 12).final.core.queries = 2 := Kernels.ReleaseAcquireMessage.source_oracle_queries_are_preserved

abbrev retryOracle := Kernels.ReleaseAcquireMessage.retryOracle

abbrev retryResult := Kernels.ReleaseAcquireMessage.retryResult

abbrev retryTrace := Kernels.ReleaseAcquireMessage.retryTrace

theorem polling_retry_is_an_actual_source_run : Ordered.Produced code bindings block retryTrace := Kernels.ReleaseAcquireMessage.polling_retry_is_an_actual_source_run

theorem polling_retry_retains_both_acquires : (retryTrace.events.map fun kind => kind.order) =
    [.acquire,.acquire,.weak,.weak] := Kernels.ReleaseAcquireMessage.polling_retry_retains_both_acquires

theorem polling_retry_consumes_three_queries : retryTrace.final.core.queries = 3 := Kernels.ReleaseAcquireMessage.polling_retry_consumes_three_queries

theorem ordered_integer_load_rejects_a_real_oracle_reply :
    (Ordered.run (context 1) (fun _ => .real .f32 0)
      [.load .acquire .gpu "%seen" ⟨.imm 64,0⟩] 1 {}).toOption.isNone = true := Kernels.ReleaseAcquireMessage.ordered_integer_load_rejects_a_real_oracle_reply

abbrev payloadWrite := Kernels.ReleaseAcquireMessage.payloadWrite

abbrev flagWrite := Kernels.ReleaseAcquireMessage.flagWrite

abbrev flagRead := Kernels.ReleaseAcquireMessage.flagRead

abbrev payloadRead := Kernels.ReleaseAcquireMessage.payloadRead

abbrev flag := Kernels.ReleaseAcquireMessage.flag

abbrev payload := Kernels.ReleaseAcquireMessage.payload

abbrev rf := Kernels.ReleaseAcquireMessage.rf

theorem flag_endpoints_are_mutually_strong : Ordered.MorallyStrong candidate flagWrite flagRead := Kernels.ReleaseAcquireMessage.flag_endpoints_are_mutually_strong

theorem flag_read_observes_release : Ordered.Observed candidate rf flagWrite flagRead := Kernels.ReleaseAcquireMessage.flag_read_observes_release

theorem direct_release_acquire_synchronizes : Ordered.ReleaseAcquireSync candidate rf flagWrite flagRead := Kernels.ReleaseAcquireMessage.direct_release_acquire_synchronizes

theorem producer_payload_precedes_release : Ptx.Event.ProgramOrder candidate.view payloadWrite flagWrite := Kernels.ReleaseAcquireMessage.producer_payload_precedes_release

theorem consumer_acquire_precedes_payload : Ptx.Event.ProgramOrder candidate.view flagRead payloadRead := Kernels.ReleaseAcquireMessage.consumer_acquire_precedes_payload

theorem payload_publication_is_causal : Ordered.BaseCausality candidate rf payloadWrite payloadRead := Kernels.ReleaseAcquireMessage.payload_publication_is_causal

/-- A graph-only scope regression. No source provenance or legal execution is
claimed for this deliberately constructed two-CTA graph. -/
def crossCandidate (writerScope readerScope : Scope) : Ordered.Candidate :=
  ⟨[⟨id 0,oracle,0,{},[⟨.write flag (Scalar.u32Bytes 1),.release,some writerScope⟩]⟩,
    ⟨⟨⟨1,0,0⟩,.zero⟩,oracle,0,{},[⟨.read flag (Scalar.u32Bytes 1),.acquire,some readerScope⟩]⟩]⟩
def crossWriter : Ptx.Event.EventId := ⟨id 0,0⟩
def crossReader : Ptx.Event.EventId := ⟨⟨⟨1,0,0⟩,.zero⟩,0⟩

theorem cta_release_does_not_cover_other_cta (readerScope : Scope) :
    ¬Ordered.MorallyStrong (crossCandidate .cta readerScope) crossWriter crossReader := by
  rintro ⟨hs,_⟩
  rcases hs with he | ⟨sa,sb,hsa,_,ha,_⟩
  · have h := congrArg (fun thread => thread.cta.x) he
    norm_num [crossWriter,crossReader,id,Kernels.ReleaseAcquireMessage.id,Dim3.zero] at h
  · have he : sa = .cta := by simpa [crossCandidate,crossWriter,crossReader,id,Ordered.Candidate.kindAt,Ordered.Kind.strongScope] using hsa.symm
    subst sa
    norm_num [Scope.Includes,crossWriter,crossReader,id,Kernels.ReleaseAcquireMessage.id,Dim3.zero] at ha

theorem release_qualifier_is_not_a_global_fence :
    ¬Ordered.ReleaseAcquireSync (crossCandidate .cta .gpu) rf crossWriter crossReader := by
  exact fun hs => cta_release_does_not_cover_other_cta .gpu hs.2.2.1

end
end Ptx.OrderedTests
