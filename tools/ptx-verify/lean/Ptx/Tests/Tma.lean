import Ptx.Hopper.TmaControl
import Ptx.Generated.HopperTmaCopy
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Permutation

/-! Actual 2-D TMA source with a padded input layout, byte-accurate copy metadata
and a source-derived implicit notification. This is not yet a complete combined
memory/proxy/observer witness or a hardware execution test. -/
namespace Ptx.TmaTests
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def view : Tma.Descriptor2D := ⟨128,16,8,64,8,2,2⟩
def coords : Tma.Coordinates := ⟨2,1⟩
def initial (location : Location) : Symbolic.Byte := .bits (byte location.address)
def payload : List Symbolic.Byte := List.ofFn (fun offset : Fin 32 => Tma.byteValue view coords initial offset.val)
def oracle : Oracle := {
  ampere := {scalar := fun _ => .integer 0,bytes := fun _ => []}
  wait := fun _ => true
  descriptor := fun _ => view
  tmaBytes := fun _ => payload
}
def id : ThreadId := ⟨.zero,.zero⟩
def ctx : Scalar.Context := {id := id,params := [("MAP",4096)],block := .one}
def loc : Location := ⟨.shared .zero,0⟩
def copy : TmaCopy := ⟨4096,view,coords,16,0,0,payload⟩
def events : List Hopper.Event := [.barrier ⟨loc,.init 1⟩,.proxyFenceAsyncShared .zero,
  .barrier ⟨loc,.arriveExpectTx 32⟩,.tmaIssue copy,.barrier ⟨loc,.tryWaitParity 0 true⟩,.barrier ⟨loc,.inval⟩]
def done : State := {
  scalar := {
    core := {
      thread := {pc := 12,regs := [("%ready",1),("%y",1),("%x",2),("%dst",16),("%bar",0),("%map",4096)],status := .done}
      queries := 3
    }
  }
}
def trace : ThreadTrace := ⟨id,oracle,13,done,events⟩
def candidate : Candidate := ⟨[trace]⟩
def launch : Scalar.Launch := ⟨⟨.one,.one⟩,[("MAP",4096)],initial⟩
def eid (serial : Nat) : Ptx.Event.EventId := ⟨id,serial⟩
def operation : Tma.CopyId := ⟨eid 3⟩

theorem profile : Tma.Profile view := by decide
theorem actual_source : Produced Generated.hopper_tma_copy.program ctx.params .one trace := by rfl
theorem formed : WellFormed Generated.hopper_tma_copy.program launch candidate := by
  refine ⟨by norm_num [launch,Geometry.Valid,Dim3.Positive,Dim3.one],by simp [candidate],?_,?_⟩
  · intro t ht
    have he : t = trace := List.mem_singleton.mp ht
    subst t
    exact ⟨by norm_num [trace,id,launch,ThreadId.Valid,Dim3.Within,Dim3.one,Dim3.zero],actual_source⟩
  · intro who hv
    have he : who = id := by
      rcases who with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
      change (cx < 1 ∧ cy < 1 ∧ cz < 1) ∧ (tx < 1 ∧ ty < 1 ∧ tz < 1) at hv
      have hh : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ tx = 0 ∧ ty = 0 ∧ tz = 0 := by omega
      rcases hh with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      rfl
    exact ⟨trace,List.mem_singleton_self _,he.symm⟩
theorem complete : Complete candidate := by intro t ht; cases List.mem_singleton.mp ht; rfl

theorem copy_from_actual_issue : Tma.copyAt candidate operation = some copy := by rfl
theorem actual_copy_size : copy.payload.length = copy.descriptor.bytes := tma_copy_payload_length formed copy_from_actual_issue
theorem actual_issue_pc : sourcePC candidate Generated.hopper_tma_copy.program ctx.params .one (eid 3) = some 8 := by rfl
theorem actual_query_base : copy.queryBase = 0 ∧ done.scalar.core.queries = 3 := by decide

theorem first_global_byte : Tma.readLocation candidate operation 0 = some ⟨.global,196⟩ := by decide
theorem next_row_respects_stride : Tma.readLocation candidate operation 16 = some ⟨.global,260⟩ := by decide
theorem last_destination_byte : Tma.writeLocation Tma.localShared candidate operation 31 = some ⟨.shared .zero,47⟩ := by decide
theorem after_destination_absent : Tma.writeLocation Tma.localShared candidate operation 32 = none := by decide

theorem payload_byte (offset : Fin 32) : payload[offset.val]? = some (Tma.byteValue view coords initial offset.val) := by
  fin_cases offset <;> rfl

theorem copies_exact : Tma.copies candidate = [operation] := by rfl
theorem payload_agrees : Tma.PayloadAgreement candidate initial := by
  intro actual op he offset ho
  have hm := Tma.copy_present_mem he
  rw [copies_exact] at hm
  have hid := List.mem_singleton.mp hm
  subst actual
  have hc : op = copy := Option.some.inj (he.symm.trans copy_from_actual_issue)
  subst op
  exact payload_byte ⟨offset,ho⟩

def maps (address : Nat) : Option Tma.Descriptor2D := if address = 4096 then some view else none

theorem descriptor_agrees : Tma.DescriptorAgreement candidate maps := by
  intro actual op he
  have hm := Tma.copy_present_mem he
  rw [copies_exact] at hm
  have hid := List.mem_singleton.mp hm
  subst actual
  have hc : op = copy := Option.some.inj (he.symm.trans copy_from_actual_issue)
  subst op
  rfl

def history : List Tma.Entry :=
  [⟨.source (eid 0),.init 1⟩,⟨.source (eid 2),.arriveExpectTx 32⟩,
   ⟨.notification operation,.completeTx 32⟩,⟨.source (eid 4),.tryWaitParity 0 true⟩,⟨.source (eid 5),.inval⟩]

theorem notification_is_exact : Tma.notification Tma.localShared candidate operation = some ⟨loc,.completeTx 32⟩ := by rfl
theorem history_valid : Tma.HistoryValid Tma.localShared candidate loc history := ⟨by decide,by decide,by decide,⟨none,by decide⟩⟩
theorem wait_has_real_phase : ∃ state, candidate.barrierAt (eid 4) = some ⟨loc,.tryWaitParity 0 true⟩ ∧
    Mbarrier.WellFormed state ∧ Mbarrier.run none ((history.map Tma.Entry.operation).take 3) = some (some state) ∧
    0 < state.phase ∧ 0%2 ≠ state.phase%2 := Tma.history_successful_wait_phase history_valid rfl

theorem source_only_history_is_insufficient : Mbarrier.run none [.init 1,.arriveExpectTx 32,.tryWaitParity 0 true,.inval] = none := by decide

def duplicateNotify := history.take 3 ++ [⟨Tma.Origin.notification operation,.completeTx 32⟩] ++ history.drop 3

theorem duplicate_notification_rejected : ¬ (duplicateNotify.map Tma.Entry.origin).Nodup := by decide
theorem duplicate_protocol_alone_passes : Mbarrier.Admitted (duplicateNotify.map Tma.Entry.operation) := ⟨none,by decide⟩

def histories (where_ : Location) : List Tma.Entry := if where_ = loc then history else []

theorem all_resource_locations : ∀ actual ∈ Tma.origins candidate, ∀ data,
    Tma.resourceAt Tma.localShared candidate actual = some data → data.location = loc := by decide

theorem all_histories : ∀ where_, Tma.HistoryValid Tma.localShared candidate where_ (histories where_) := by
  intro where_
  by_cases hl : where_ = loc
  · subst where_
    exact history_valid
  · have hinv : Tma.inventory Tma.localShared candidate where_ = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro entry he
      have hs := Tma.inventory_iff.mp he
      have ho := Tma.origin_mem hs
      exact hl (all_resource_locations entry.origin ho _ hs)
    refine ⟨by simp [histories,hl],?_,?_,?_⟩
    · simp [histories,hl,hinv]
    · simp [histories,hl,Tma.SourceOrder]
    · exact ⟨none,by simp [histories,hl,Mbarrier.run]⟩

def rank : Tma.Node → Nat
  | .source event => if event.serial < 4 then event.serial else event.serial+67
  | .descriptor _ => 4
  | .read _ offset => 5+2*offset
  | .write _ offset => 6+2*offset
  | .notify _ => 70

theorem only_copy {actual op} (he : Tma.copyAt candidate actual = some op) : actual = operation ∧ op = copy := by
  have hm := Tma.copy_present_mem he
  rw [copies_exact] at hm
  have hid := List.mem_singleton.mp hm
  subst actual
  exact ⟨rfl,Option.some.inj (he.symm.trans copy_from_actual_issue)⟩

theorem source_rank : ∀ a b, Tma.ProgramOrder candidate a b → rank a < rank b := by
  intro a b he
  cases a <;> cases b <;> simp only [Tma.ProgramOrder] at he
  have hh := he.2.2.2
  simp only [rank]
  split_ifs <;> omega

theorem cta_rank : ∀ a b, Tma.CTAControl candidate a b → rank a < rank b := by
  have hn : ∀ a ∈ candidate.eventIds, ∀ b ∈ candidate.eventIds, ¬ Hopper.CTAControl candidate a b := by decide
  intro a b he
  cases a <;> cases b <;> simp only [Tma.CTAControl] at he
  have hp := Hopper.cta_control_present he
  exact (hn _ (present_mem_eventIds hp.1) _ (present_mem_eventIds hp.2) he).elim

theorem internal_rank : ∀ a b, Tma.InternalEdge candidate a b → rank a < rank b := by
  intro a b he
  cases he with
  | issue he =>
    obtain ⟨op,hop⟩ := Option.isSome_iff_exists.mp he
    obtain ⟨rfl,_⟩ := only_copy hop
    decide
  | descriptorRead he =>
    simp only [rank]
    omega
  | descriptorWrite he =>
    simp only [rank]
    omega
  | data he => simp [rank]
  | complete he =>
    obtain ⟨op,hcopy,hoff⟩ := Tma.write_has_copy he
    obtain ⟨rfl,rfl⟩ := only_copy hcopy
    change _ < 32 at hoff
    simp only [rank]
    omega

theorem resource_rank : ∀ a b, Tma.ResourceEdge histories a b → rank a < rank b := by
  have hr : ∀ a ∈ history, ∀ b ∈ history, Tma.Before history a.origin b.origin → rank a.origin.node < rank b.origin.node := by decide
  rintro a b ⟨where_,left,hl,right,hrr,hbefore,rfl,rfl⟩
  by_cases he : where_ = loc
  · subst where_
    exact hr left hl right hrr hbefore
  · simp [histories,he] at hl

theorem control_acyclic : Tma.ControlAcyclic candidate histories :=
  Tma.control_acyclic_of_rank rank source_rank cta_rank internal_rank resource_rank

theorem source_bytes_resources_control : Tma.Components Generated.hopper_tma_copy.program launch candidate Tma.localShared maps histories :=
  ⟨formed,complete,descriptor_agrees,payload_agrees,all_histories,control_acyclic⟩

theorem negative_coordinate_word : Tma.signed32 4294967295 = -1 := by decide
theorem negative_coordinate_zero_fill : Tma.sourceByte view ⟨-1,1⟩ 0 = none ∧ Tma.sourceByte view ⟨-1,1⟩ 1 = none := by decide
theorem following_element_is_in_bounds : Tma.sourceByte view ⟨-1,1⟩ 2 = some ⟨.global,192⟩ := by decide
theorem zero_fill_is_a_byte_rule : Tma.byteValue view ⟨-1,1⟩ initial 0 = .bits (byte 0) := by rfl

def shortOracle : Oracle := {oracle with tmaBytes := fun _ => List.replicate 31 (.bits (byte 0))}
theorem short_payload_rejected : Hopper.run ctx shortOracle Generated.hopper_tma_copy.program 13 {} = .error (.tmaPayloadSize 32 31) := by rfl

def badCopy : TmaCopy := {copy with payload := List.replicate 32 (.bits (byte 0))}
def badEvents : List Hopper.Event := [.barrier ⟨loc,.init 1⟩,.proxyFenceAsyncShared .zero,
  .barrier ⟨loc,.arriveExpectTx 32⟩,.tmaIssue badCopy,.barrier ⟨loc,.tryWaitParity 0 true⟩,.barrier ⟨loc,.inval⟩]
def badTrace : ThreadTrace := {trace with oracle := {oracle with tmaBytes := fun _ => badCopy.payload},events := badEvents}
def badCandidate : Candidate := ⟨[badTrace]⟩
theorem wrong_bytes_source_returns : Produced Generated.hopper_tma_copy.program ctx.params .one badTrace := by rfl
theorem wrong_bytes_resource_history_passes : Tma.HistoryValid Tma.localShared badCandidate loc history :=
  ⟨by decide,by decide,by decide,⟨none,by decide⟩⟩
theorem wrong_bytes_not_agreed : ¬ Tma.PayloadAgreement badCandidate initial := by
  intro h
  have hh := h operation badCopy (by rfl) 0 (by decide)
  change some (Symbolic.Byte.bits (byte 0)) = some (Symbolic.Byte.bits (byte 196)) at hh
  have he := Symbolic.Byte.bits.inj (Option.some.inj hh)
  exact (by decide : byte 0 ≠ byte 196) he

def shortView : Tma.Descriptor2D := {view with boxHeight := 1}
def countCopy : TmaCopy := {copy with descriptor := shortView,payload := payload.take 16}
def countEvents : List Hopper.Event := [.barrier ⟨loc,.init 1⟩,.proxyFenceAsyncShared .zero,
  .barrier ⟨loc,.arriveExpectTx 32⟩,.tmaIssue countCopy,.barrier ⟨loc,.tryWaitParity 0 true⟩,.barrier ⟨loc,.inval⟩]
def countTrace : ThreadTrace := {trace with oracle := {oracle with descriptor := fun _ => shortView,tmaBytes := fun _ => countCopy.payload},events := countEvents}
def countCandidate : Candidate := ⟨[countTrace]⟩
theorem count_mismatch_source_returns : Produced Generated.hopper_tma_copy.program ctx.params .one countTrace := by rfl

theorem every_count_order_rejected : ∀ entries ∈ (Tma.inventory Tma.localShared countCandidate loc).permutations',
    (Mbarrier.run none (entries.map Tma.Entry.operation)).isSome = false := by decide

theorem no_count_mismatch_history (entries : List Tma.Entry) : ¬ Tma.HistoryValid Tma.localShared countCandidate loc entries := by
  intro h
  have hh := every_count_order_rejected entries (List.mem_permutations'.mpr h.exhaustive)
  obtain ⟨last,hr⟩ := h.protocol
  rw [hr] at hh
  cases hh

end
end Ptx.TmaTests
