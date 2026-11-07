import Ptx.Hopper.ProxyPublication
import Ptx.Tests.TmaInputValues
import Ptx.Generated.HopperTmaPublish

/-! Actual TMA/shared-load/global-store source family. Correctness rules below
are relative to the explicit proxy visibility fragment, not full Hopper allowed
execution, observer, race, allocation or CUDA runtime admission. -/
namespace Ptx.TmaPublicationTests
open Ptx.ISA Ptx.Hopper
open Ptx.TmaTests (view copy operation loc)
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def answer : Nat := 3351692740
def bytes (n : Nat) : List Symbolic.Byte := (encodeU32 (wrap 32 n)).map Symbolic.Byte.bits
def oracle (n : Nat) : Oracle := {TmaTests.oracle with ampere := {TmaTests.oracle.ampere with scalar := fun _ => .integer n}}
def params : Bindings := [("MAP",4096),("OUT",8192)]
def events (n : Nat) : List Hopper.Event :=
  [.barrier ⟨loc,.init 1⟩,.proxyFenceAsyncShared .zero,.barrier ⟨loc,.arriveExpectTx 32⟩,.tmaIssue copy,
   .barrier ⟨loc,.tryWaitParity 0 true⟩,.ampere (.ordinary (.read ⟨.shared .zero,16⟩ (bytes n))),
   .ampere (.ordinary (.write ⟨.global,8192⟩ (bytes n))),.barrier ⟨loc,.inval⟩]
def done (n : Nat) : State := {
  scalar := {
    core := {
      thread := {pc := 15,regs := [("%value",wrap 32 n),("%ready",1),("%y",1),("%x",2),("%dst",16),("%bar",0),("%out",8192),("%map",4096)],status := .done}
      queries := 4
    }
  }
}
def trace (n : Nat) : ThreadTrace := ⟨TmaTests.id,oracle n,16,done n,events n⟩
def candidate (n : Nat) : Candidate := ⟨[trace n]⟩
def launch : Scalar.Launch := ⟨⟨.one,.one⟩,params,TmaTests.initial⟩
def eid := TmaTests.eid
def history : List Tma.Entry :=
  [⟨.source (eid 0),.init 1⟩,⟨.source (eid 2),.arriveExpectTx 32⟩,
   ⟨.notification operation,.completeTx 32⟩,⟨.source (eid 4),.tryWaitParity 0 true⟩,⟨.source (eid 7),.inval⟩]
def histories (where_ : Location) : List Tma.Entry := if where_ = loc then history else []
def cluster : Access.ClusterScope := fun a b => a.cta = b.cta

theorem actual_source (n : Nat) : Produced Generated.hopper_tma_publish.program params .one (trace n) := by rfl
theorem formed (n : Nat) : WellFormed Generated.hopper_tma_publish.program launch (candidate n) := by
  refine ⟨by norm_num [launch,Geometry.Valid,Dim3.Positive,Dim3.one],by simp [candidate],?_,?_⟩
  · intro t ht
    have he : t = trace n := List.mem_singleton.mp ht
    subst t
    exact ⟨by norm_num [trace,TmaTests.id,launch,ThreadId.Valid,Dim3.Within,Dim3.one,Dim3.zero],actual_source n⟩
  · intro who hv
    have he : who = TmaTests.id := by
      rcases who with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
      change (cx < 1 ∧ cy < 1 ∧ cz < 1) ∧ (tx < 1 ∧ ty < 1 ∧ tz < 1) at hv
      have hh : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ tx = 0 ∧ ty = 0 ∧ tz = 0 := by omega
      rcases hh with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      rfl
    exact ⟨trace n,List.mem_singleton_self _,he.symm⟩
theorem complete (n : Nat) : Complete (candidate n) := by intro t ht; cases List.mem_singleton.mp ht; rfl
theorem only_copy {n actual op} (hc : Tma.copyAt (candidate n) actual = some op) : actual = operation ∧ op = copy := by
  have hm := Tma.copy_present_mem hc
  have hx : Tma.copies (candidate n) = [operation] := by rfl
  rw [hx] at hm
  have hid := List.mem_singleton.mp hm
  subst actual
  exact ⟨rfl,Option.some.inj (hc.symm.trans (show Tma.copyAt (candidate n) operation = some copy by rfl))⟩
theorem history_valid (n : Nat) : Tma.HistoryValid Tma.localShared (candidate n) loc history :=
  ⟨by decide,by change history.Perm (Tma.inventory Tma.localShared (candidate 0) loc); decide,by decide,⟨none,by decide⟩⟩
theorem notice_stamp : Tma.stampBefore history 2 = some ⟨1,0⟩ := by decide
theorem wait_stamp : Tma.stampBefore history 3 = some ⟨1,1⟩ := by decide
theorem observed : Tma.observation history 2 3 = some (operation,eid 4) := by decide
theorem actual_completion_observed (n : Nat) : Access.CompletionObserved Tma.localShared (candidate n) histories cluster operation (eid 4) :=
  ⟨rfl,loc,2,3,rfl,by simpa [histories] using history_valid n,by simpa [histories] using observed⟩
theorem consumer_after_wait (n : Nat) : Access.GenericAfter (candidate n) (eid 4) (eid 5) :=
  Access.generic_program_after ⟨by rfl,by simp [Candidate.Present,Candidate.eventAt,Candidate.traceAt,candidate,trace,events,eid,TmaTests.eid],rfl,by decide⟩
theorem byte_published (n : Nat) (offset : Fin 4) : Access.Published Tma.localShared (candidate n) histories cluster
    (.tma (.write operation offset.val)) (.tma (.source (eid 5))) ⟨.shared .zero,16+offset.val⟩ := by
  refine ⟨eid 4,?_,rfl,actual_completion_observed n,consumer_after_wait n⟩
  fin_cases offset <;> rfl

theorem event_member {n event e} (he : (candidate n).eventAt event = some e) : e ∈ events n := by
  obtain ⟨t,ht,_,hg⟩ := Ptx.Hopper.eventAt_trace he
  have ht : t = trace n := List.mem_singleton.mp ht
  subst t
  exact List.mem_of_getElem? hg

theorem no_nonbulk (n : Nat) (event : Ptx.Event.EventId) : Access.copyAt (candidate n) event = none := by
  cases hc : Access.copyAt (candidate n) event with
  | none => rfl
  | some op =>
    obtain ⟨ordinal,he⟩ := Access.nonbulk_has_actual_issue hc
    have hm := event_member he
    simp [events] at hm

theorem source_memory_shape {n event k}
    (hk : Access.kind Tma.localShared Access.globalDescriptor (candidate n) (.tma (.source event)) = some k) :
    k = .read ⟨.shared .zero,16⟩ (bytes n) ∨ k = .write ⟨.global,8192⟩ (bytes n) := by
  cases he : (candidate n).eventAt event with
  | none => simp [Access.kind,he] at hk
  | some e =>
    have hm := event_member he
    simp only [events,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [Access.kind]

theorem unique_shared_writer {n writer location value}
    (hl : location.space = .shared .zero)
    (hw : Access.writeByte Tma.localShared Access.globalDescriptor (candidate n) writer location = some value) :
    writer = .tma (.write operation (location.address-16)) := by
  cases writer with
  | copyRead issue | copyWrite issue => simp [Access.writeByte,Access.kind,no_nonbulk] at hw
  | tma node =>
    cases node with
    | source event =>
      cases hk : Access.kind Tma.localShared Access.globalDescriptor (candidate n) (.tma (.source event)) with
      | none => simp [Access.writeByte,hk] at hw
      | some k =>
        rcases source_memory_shape hk with rfl | rfl
        · simp [Access.writeByte,hk,Ptx.Event.Kind.writeByte] at hw
        · simp [Access.writeByte,hk,Ptx.Event.Kind.writeByte,Ptx.Event.payloadByte,hl] at hw
    | descriptor id => rw [Access.descriptor_no_write] at hw; cases hw
    | read id offset => rw [Access.tensor_read_no_write] at hw; cases hw
    | notify id => cases hw
    | write actual offset =>
      cases hc : Tma.copyAt (candidate n) actual with
      | none => simp [Access.writeByte,Access.kind,Tma.writeLocation,hc] at hw
      | some op =>
        obtain ⟨rfl,rfl⟩ := only_copy hc
        by_cases ho : offset < copy.descriptor.bytes
        · change offset < view.bytes at ho
          cases hb : Tma.transferByte (candidate n) operation offset with
          | none => simp [Access.writeByte,Access.kind,hb] at hw
          | some b =>
            have hloc : Tma.writeLocation Tma.localShared (candidate n) operation offset = some ⟨.shared .zero,16+offset⟩ := by
              simp only [Tma.writeLocation,hc,Option.bind_some]
              have hop : offset < copy.descriptor.bytes := ho
              rw [if_pos hop]
              rfl
            have hk : Access.kind Tma.localShared Access.globalDescriptor (candidate n) (.tma (.write operation offset)) =
                some (.write ⟨.shared .zero,16+offset⟩ [b]) := by simp [Access.kind,hloc,hb]
            have hs : Ptx.Event.payloadByte (⟨.shared .zero,16+offset⟩ : Location) [b] location = some value := by
              simpa only [Access.writeByte,hk,Option.bind_some,Ptx.Event.Kind.writeByte] using hw
            have he := (Access.singleton_payload hs).1
            have ha := congrArg Location.address he
            have hoff : location.address-16 = offset := by simp only at ha; omega
            simp [hoff]
        · simp [Access.writeByte,Access.kind,Tma.writeLocation,hc,ho] at hw

theorem consumer_read (n : Nat) (offset : Fin 4) : Access.readByte Tma.localShared Access.globalDescriptor (candidate n)
    (.tma (.source (eid 5))) ⟨.shared .zero,16+offset.val⟩ =
      some (.bits (byte (n / 2^(8*offset.val)))) := by
  fin_cases offset <;> simp [Access.readByte,Access.kind,Candidate.eventAt,Candidate.traceAt,candidate,trace,events,eid,
    TmaTests.eid,bytes,Ptx.Event.Kind.readByte,Ptx.Event.payloadByte,encodeU32,wrap,byte]
  all_goals omega

theorem copy_write (n : Nat) (offset : Fin 4) : Access.writeByte Tma.localShared Access.globalDescriptor (candidate n)
    (.tma (.write operation offset.val)) ⟨.shared .zero,16+offset.val⟩ = some (.bits (byte (196+offset.val))) := by
  fin_cases offset <;> rfl

/-- Every source reply in this family is constrained by visibility admission;
the consumer byte is not a postcondition or oracle premise of the rule. -/
theorem consumer_value {n initial eligible rf co} (offset : Fin 4)
    (hv : Access.VisibilityConditions Tma.localShared Access.globalDescriptor (candidate n) initial eligible rf co histories cluster)
    (he : eligible (.tma (.source (eid 5))) ⟨.shared .zero,16+offset.val⟩) :
    byte (n / 2^(8*offset.val)) = byte (196+offset.val) := by
  have hh := Access.published_unique_writer_value hv he (copy_write n offset) (consumer_read n offset) (byte_published n offset)
    (fun _ _ hw => by simpa using unique_shared_writer rfl hw)
  exact Symbolic.Byte.bits.inj hh

def ConsumerSite (read : Access.Node) (location : Location) : Prop :=
  read = .tma (.source (eid 5)) ∧ location.space = .shared .zero ∧ 16 ≤ location.address ∧ location.address < 20
def rf : Access.ReadsFrom := fun _ location =>
  if location.space = .shared .zero ∧ 16 ≤ location.address ∧ location.address < 20 then
    some (.tma (.write operation (location.address-16))) else none
def co (location : Location) (left right : Option Access.Node) : Prop :=
  left = none ∧ ∃ writer, right = some writer ∧
    (Access.writeByte Tma.localShared Access.globalDescriptor (candidate answer) writer location).isSome = true

theorem answer_from_initial_input : answer = decodeLE [byte 196,byte 197,byte 198,byte 199] := by rfl

theorem witness_agreement : Access.ReadAgreement Tma.localShared Access.globalDescriptor (candidate answer)
    TmaInputTests.initial ConsumerSite rf := by
  rintro read location value ⟨rfl,hspace,hlo,hhi⟩ hr
  rcases location with ⟨space,address⟩
  simp only at hspace hlo hhi
  subst space
  have ha : address = 16 ∨ address = 17 ∨ address = 18 ∨ address = 19 := by omega
  rcases ha with rfl | rfl | rfl | rfl
  all_goals
    change Access.writeByte Tma.localShared Access.globalDescriptor (candidate answer)
      (.tma (.write operation _)) _ = some value
    exact (show Access.writeByte Tma.localShared Access.globalDescriptor (candidate answer) _ _ =
      Access.readByte Tma.localShared Access.globalDescriptor (candidate answer) _ _ by rfl).trans hr

theorem witness_visibility : Access.VisibilityConditions Tma.localShared Access.globalDescriptor (candidate answer)
    TmaInputTests.initial ConsumerSite rf co histories cluster := by
  refine ⟨witness_agreement,?_,?_,?_⟩
  · intro writer location value hw
    exact ⟨rfl,writer,rfl,by rw [hw]; rfl⟩
  · rintro writer read location vw vr ⟨rfl,hspace,hlo,hhi⟩ hw _ _ ⟨hfirst,_⟩
    have hs : rf (.tma (.source (eid 5))) location = some (.tma (.write operation (location.address-16))) := by
      simp [rf,hspace,hlo,hhi]
    rw [hs] at hfirst
    cases hfirst
  · rintro read writer location vr vw ⟨rfl,hspace,_,_⟩ _ hw hp
    have hid := unique_shared_writer hspace hw
    subst writer
    obtain ⟨fence,_,hbefore,hafter,_,_⟩ := hp
    have hb := hbefore.2.2.2
    have ha := hafter.2.2.2
    change 5 < fence.serial at hb
    change fence.serial < 3 at ha
    omega

theorem consumer_word {n initial eligible rfs cos}
    (hv : Access.VisibilityConditions Tma.localShared Access.globalDescriptor (candidate n) initial eligible rfs cos histories cluster)
    (he : ∀ offset : Fin 4, eligible (.tma (.source (eid 5))) ⟨.shared .zero,16+offset.val⟩) : wrap 32 n = answer := by
  have h0 := consumer_value ⟨0,by decide⟩ hv (he ⟨0,by decide⟩)
  have h1 := consumer_value ⟨1,by decide⟩ hv (he ⟨1,by decide⟩)
  have h2 := consumer_value ⟨2,by decide⟩ hv (he ⟨2,by decide⟩)
  have h3 := consumer_value ⟨3,by decide⟩ hv (he ⟨3,by decide⟩)
  have hbytes : encodeU32 n = encodeU32 answer := by
    change [byte n,byte (n/256),byte (n/65536),byte (n/16777216)] = [byte 196,byte 197,byte 198,byte 199]
    simp only [Nat.mul_zero,Nat.mul_one,Nat.pow_zero,Nat.div_one,Nat.add_zero] at h0 h1 h2 h3
    change byte (n/256) = byte 197 at h1
    change byte (n/65536) = byte 198 at h2
    change byte (n/16777216) = byte 199 at h3
    rw [h0,h1,h2,h3]
  have hword := congrArg decodeLE hbytes
  simpa [decode_encodeU32,wrap,answer] using hword

theorem checked_fragment_instance : wrap 32 answer = 3351692740 :=
  consumer_word witness_visibility (fun offset => ⟨rfl,rfl,by change 16 ≤ 16+offset.val; omega,by change 16+offset.val < 20; have hh := offset.isLt; omega⟩)

theorem zero_reply_rejected_for_every_rf_co {initial eligible rfs cos}
    (he : eligible (.tma (.source (eid 5))) ⟨.shared .zero,16⟩) :
    ¬ Access.VisibilityConditions Tma.localShared Access.globalDescriptor (candidate 0) initial eligible rfs cos histories cluster := by
  intro hv
  have hh := consumer_value ⟨0,by decide⟩ hv he
  exact (by decide : byte 0 ≠ byte 196) hh

theorem actual_consumer_pc (n : Nat) : sourcePC (candidate n) Generated.hopper_tma_publish.program params .one (eid 5) = some 12 := by rfl
theorem actual_store_pc (n : Nat) : sourcePC (candidate n) Generated.hopper_tma_publish.program params .one (eid 6) = some 13 := by rfl
theorem actual_store_value {n initial eligible rfs cos}
    (hv : Access.VisibilityConditions Tma.localShared Access.globalDescriptor (candidate n) initial eligible rfs cos histories cluster)
    (he : ∀ offset : Fin 4, eligible (.tma (.source (eid 5))) ⟨.shared .zero,16+offset.val⟩) :
    Access.kind Tma.localShared Access.globalDescriptor (candidate n) (.tma (.source (eid 6))) =
      some (.write ⟨.global,8192⟩ (bytes answer)) := by
  have hword := consumer_word hv he
  change some (Ptx.Event.Kind.write ⟨.global,8192⟩ (bytes n)) = _
  unfold bytes
  rw [hword]
  rfl

end
end Ptx.TmaPublicationTests
