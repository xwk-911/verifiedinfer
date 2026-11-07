import Ptx.Kernels.AmpereTiledInventory
import Ptx.Ampere.Checked

/-! Inventories for every actual well-formed complete active candidate. SourceInfo
only bundles existing launch/provenance/completion premises; it supplies no
access inventory, race/order/value assumption or selected memory witness. -/
namespace Ptx.AmpereTiledGraph
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledEvents
noncomputable section
abbrev code := Generated.ampere_tiled_matmul.program

def context (launch : Scalar.Launch) (id : ThreadId) : Scalar.Context :=
  {id := id,params := launch.params,block := launch.geometry.block}
structure SourceInfo (cfg : Config) (launch : Scalar.Launch) (candidate : Candidate) : Prop where
  layout : Layout cfg
  params : AmpereTiledInit.Params cfg launch.params
  geometry : launch.geometry = geometry cfg
  active : Active cfg
  formed : WellFormed code launch candidate
  complete : Complete candidate

theorem source_of_pre {cfg a b launch candidate} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hw : WellFormed code launch candidate) (hc : Complete candidate) : SourceInfo cfg launch candidate := by
  refine ⟨hp.1,?_,hp.2.2.1,ha,hw,hc⟩
  rw [hp.2.2.2]
  exact AmpereTiledInit.canonical_params cfg

theorem trace_view {cfg launch candidate} (h : SourceInfo cfg launch candidate) {t : ThreadTrace}
    (ht : t ∈ candidate.traces) : ∃ r : ReplySet cfg (context launch t.id) t.oracle,
    t.count = 64+21*(cfg.k/16) ∧ t.final = finalState cfg (context launch t.id) t.oracle r ∧
      t.events = events cfg (context launch t.id) t.oracle r :=
  candidate_trace_shape h.layout h.params h.geometry h.active h.formed h.complete ht

theorem event_view {cfg launch candidate event kind} (h : SourceInfo cfg launch candidate)
    (he : candidate.eventAt event = some kind) :
    ∃ t ∈ candidate.traces, t.id = event.thread ∧ ∃ r : ReplySet cfg (context launch t.id) t.oracle,
      (events cfg (context launch t.id) t.oracle r)[event.serial]? = some kind := by
  obtain ⟨t,ht,hid,hget⟩ := eventAt_trace he
  obtain ⟨r,_,_,hevents⟩ := trace_view h ht
  exact ⟨t,ht,hid,r,hevents ▸ hget⟩

theorem copy_cases {cfg launch candidate operation op} (h : SourceInfo cfg launch candidate)
    (he : candidate.copyAt operation = some op) :
    ∃ t ∈ candidate.traces, ∃ r : ReplySet cfg (context launch t.id) t.oracle,
      ∃ phase, phase < cfg.k/16 ∧ ∃ part : Fin 3,
        operation = ⟨t.id,3*phase+part.val⟩ ∧ op = operationAt cfg (context launch t.id) t.oracle r phase part := by
  obtain ⟨serial,hissue⟩ := copy_has_source_issue h.formed he
  obtain ⟨t,ht,hid,r,hget⟩ := event_view h hissue
  obtain ⟨phase,hphase,part,hordinal,_,hop⟩ := AmpereTiledInventory.issue_cases hget
  refine ⟨t,ht,r,phase,hphase,part,?_,hop⟩
  cases operation
  simp_all

theorem event_of_thread_kind {candidate : Candidate} {event kind}
    (hk : candidate.memoryKind (.thread event) = some kind) : candidate.eventAt event = some (.ordinary kind) := by
  cases he : candidate.eventAt event with
  | none => simp [Candidate.memoryKind,he] at hk
  | some e =>
    cases e with
    | ordinary emitted =>
      have hh : emitted = kind := by simpa [Candidate.memoryKind,he] using hk
      subst emitted
      rfl
    | _ => simp [Candidate.memoryKind,he] at hk

theorem no_rmw {cfg launch candidate} (h : SourceInfo cfg launch candidate) (node : Node) : ¬ candidate.memoryGraph.IsRMW node := by
  rintro ⟨scope,base,bytes,hk⟩
  cases node with
  | copyRead operation | copyWrite operation =>
    cases he : candidate.copyAt operation <;> simp [Candidate.memoryGraph,Candidate.memoryKind,he] at hk
  | thread event =>
    obtain ⟨t,ht,hid,r,hget⟩ := event_view h (event_of_thread_kind hk)
    exact AmpereTiledInventory.no_rmw hget

theorem member_event {cfg launch candidate} (h : SourceInfo cfg launch candidate) {t : ThreadTrace}
    (ht : t ∈ candidate.traces) (serial : Nat) : candidate.eventAt ⟨t.id,serial⟩ = t.events[serial]? := by
  unfold Candidate.eventAt
  rw [traceAt_of_member h.formed.2.1 ht]
  rfl

theorem phase_view {cfg launch candidate} (h : SourceInfo cfg launch candidate) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase slot : Nat} (hp : phase < cfg.k/16) (hs : slot < 17) :
    ∃ t ∈ candidate.traces, t.id = id ∧ ∃ r : ReplySet cfg (context launch t.id) t.oracle,
      candidate.eventAt ⟨id,17*phase+slot⟩ = (stepEvents cfg (context launch t.id) t.oracle r phase)[slot]? := by
  obtain ⟨t,ht,hid⟩ := h.formed.2.2.2 id hv
  obtain ⟨r,_,_,he⟩ := trace_view h ht
  refine ⟨t,ht,hid,r,?_⟩
  rw [← hid,member_event h ht,he,AmpereTiledEvents.phase_event _ _ _ _ phase slot hp hs]

theorem wait_event {cfg launch candidate} (h : SourceInfo cfg launch candidate) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase : Nat} (hp : phase < cfg.k/16) :
    candidate.eventAt ⟨id,17*phase+4⟩ = some (.wait (phase+1) 0) := by
  obtain ⟨t,ht,hid,r,he⟩ := phase_view h hv hp (by decide : 4 < 17)
  rw [he,phase_events]
  rfl

theorem arrival_event {cfg launch candidate} (h : SourceInfo cfg launch candidate) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase : Nat} (hp : phase < cfg.k/16) (half : Fin 2) :
    candidate.eventAt ⟨id,17*phase+5+10*half.val⟩ = some (.ordinary (.barrierArrival 0 (2*phase+half.val))) := by
  have hs : 5+10*half.val < 17 := by have hh := half.isLt; omega
  obtain ⟨t,ht,hid,r,he⟩ := phase_view h hv hp hs
  rw [show 17*phase+5+10*half.val = 17*phase+(5+10*half.val) by omega,he,phase_events]
  fin_cases half <;> rfl

theorem return_event {cfg launch candidate} (h : SourceInfo cfg launch candidate) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase : Nat} (hp : phase < cfg.k/16) (half : Fin 2) :
    candidate.eventAt ⟨id,17*phase+6+10*half.val⟩ = some (.ordinary (.barrierReturn 0 (2*phase+half.val))) := by
  have hs : 6+10*half.val < 17 := by have hh := half.isLt; omega
  obtain ⟨t,ht,hid,r,he⟩ := phase_view h hv hp hs
  rw [show 17*phase+6+10*half.val = 17*phase+(6+10*half.val) by omega,he,phase_events]
  fin_cases half <;> rfl

theorem read_present {cfg launch candidate} (h : SourceInfo cfg launch candidate) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase : Nat} (hp : phase < cfg.k/16) (reg : Fin 6) :
    candidate.Present (.thread ⟨id,17*phase+7+reg.val⟩) := by
  have hs : 7+reg.val < 17 := by have hh := reg.isLt; omega
  obtain ⟨t,ht,hid,r,he⟩ := phase_view h hv hp hs
  change (candidate.eventAt ⟨id,17*phase+7+reg.val⟩).isSome = true
  rw [show 17*phase+7+reg.val = 17*phase+(7+reg.val) by omega,he,AmpereTiledInventory.phase_read]
  rfl

theorem copy_exists {cfg launch candidate} (h : SourceInfo cfg launch candidate) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase : Nat} (hp : phase < cfg.k/16) (part : Fin 3) :
    ∃ op, candidate.copyAt ⟨id,3*phase+part.val⟩ = some op ∧ op.group = phase ∧
      candidate.eventAt ⟨id,17*phase+part.val⟩ = some (.issue (3*phase+part.val) op) := by
  have hs : part.val < 17 := by have hh := part.isLt; omega
  obtain ⟨t,ht,hid,r,he⟩ := phase_view h hv hp hs
  rw [AmpereTiledInventory.phase_issue] at he
  exact ⟨_,event_issue_has_copy h.formed he,operation_group _ _ _ _ _ _,he⟩

theorem read_cases {cfg launch candidate node loc value} (h : SourceInfo cfg launch candidate)
    (hr : candidate.readByte node loc = some value) :
    (∃ t ∈ candidate.traces, ∃ r : ReplySet cfg (context launch t.id) t.oracle,
      ∃ phase, phase < cfg.k/16 ∧ ∃ reg : Fin 6,
        node = .thread ⟨t.id,17*phase+7+reg.val⟩ ∧
        Ptx.Event.payloadByte (AmpereTiledInventory.readBase (context launch t.id) reg)
          (AmpereTiledInventory.readPair r phase reg).encode loc = some value) ∨
    (∃ t ∈ candidate.traces, ∃ r : ReplySet cfg (context launch t.id) t.oracle,
      ∃ phase, phase < cfg.k/16 ∧ ∃ part : Fin 3,
        node = .copyRead ⟨t.id,3*phase+part.val⟩ ∧
        Ptx.Event.payloadByte (operationAt cfg (context launch t.id) t.oracle r phase part).src
          (operationAt cfg (context launch t.id) t.oracle r phase part).bytes loc = some value) := by
  cases node with
  | copyWrite operation =>
    cases hc : candidate.copyAt operation <;> simp [Candidate.readByte,Candidate.memoryKind,hc,Ptx.Event.Kind.readByte] at hr
  | copyRead operation =>
    cases hc : candidate.copyAt operation with
    | none => simp [Candidate.readByte,Candidate.memoryKind,hc] at hr
    | some op =>
      have hp : Ptx.Event.payloadByte op.src op.bytes loc = some value := by
        simpa [Candidate.readByte,Candidate.memoryKind,hc,Ptx.Event.Kind.readByte] using hr
      obtain ⟨t,ht,r,phase,hphase,part,hid,rfl⟩ := copy_cases h hc
      exact .inr ⟨t,ht,r,phase,hphase,part,congrArg Node.copyRead hid,hp⟩
  | thread event =>
    cases hk : candidate.memoryKind (.thread event) with
    | none => simp [Candidate.readByte,hk] at hr
    | some kind =>
      cases kind with
      | read base bytes =>
        have hp : Ptx.Event.payloadByte base bytes loc = some value := by simpa [Candidate.readByte,hk,Ptx.Event.Kind.readByte] using hr
        obtain ⟨t,ht,hid,r,hget⟩ := event_view h (event_of_thread_kind hk)
        obtain ⟨phase,hphase,reg,hserial,hbase,hbytes⟩ := AmpereTiledInventory.read_cases hget
        refine .inl ⟨t,ht,r,phase,hphase,reg,?_,?_⟩
        · cases event; simp_all
        · simpa only [hbase,hbytes] using hp
      | rmw scope base bytes => exact (no_rmw h (.thread event) ⟨scope,base,bytes,hk⟩).elim
      | _ => simp [Candidate.readByte,hk,Ptx.Event.Kind.readByte] at hr

theorem write_cases {cfg launch candidate node loc value} (h : SourceInfo cfg launch candidate)
    (hw : candidate.writeByte node loc = some value) :
    (∃ t ∈ candidate.traces, ∃ r : ReplySet cfg (context launch t.id) t.oracle, ∃ slot : Fin 4,
      node = .thread ⟨t.id,17*(cfg.k/16)+slot.val⟩ ∧
        Ptx.Event.payloadByte (AmpereTiledInventory.writeBase cfg (context launch t.id) slot)
          (AmpereTiledInventory.writeBytes cfg t.oracle slot) loc = some value) ∨
    (∃ t ∈ candidate.traces, ∃ r : ReplySet cfg (context launch t.id) t.oracle,
      ∃ phase, phase < cfg.k/16 ∧ ∃ part : Fin 3,
        node = .copyWrite ⟨t.id,3*phase+part.val⟩ ∧
        Ptx.Event.payloadByte (operationAt cfg (context launch t.id) t.oracle r phase part).dst
          (operationAt cfg (context launch t.id) t.oracle r phase part).bytes loc = some value) := by
  cases node with
  | copyRead operation =>
    cases hc : candidate.copyAt operation <;> simp [Candidate.writeByte,Candidate.memoryKind,hc,Ptx.Event.Kind.writeByte] at hw
  | copyWrite operation =>
    cases hc : candidate.copyAt operation with
    | none => simp [Candidate.writeByte,Candidate.memoryKind,hc] at hw
    | some op =>
      have hp : Ptx.Event.payloadByte op.dst op.bytes loc = some value := by
        simpa [Candidate.writeByte,Candidate.memoryKind,hc,Ptx.Event.Kind.writeByte] using hw
      obtain ⟨t,ht,r,phase,hphase,part,hid,rfl⟩ := copy_cases h hc
      exact .inr ⟨t,ht,r,phase,hphase,part,congrArg Node.copyWrite hid,hp⟩
  | thread event =>
    cases hk : candidate.memoryKind (.thread event) with
    | none => simp [Candidate.writeByte,hk] at hw
    | some kind =>
      cases kind with
      | write base bytes =>
        have hp : Ptx.Event.payloadByte base bytes loc = some value := by simpa [Candidate.writeByte,hk,Ptx.Event.Kind.writeByte] using hw
        obtain ⟨t,ht,hid,r,hget⟩ := event_view h (event_of_thread_kind hk)
        obtain ⟨slot,hserial,hbase,hbytes⟩ := AmpereTiledInventory.write_cases hget
        refine .inl ⟨t,ht,r,slot,?_,?_⟩
        · cases event; simp_all
        · simpa only [hbase,hbytes] using hp
      | rmw scope base bytes => exact (no_rmw h (.thread event) ⟨scope,base,bytes,hk⟩).elim
      | _ => simp [Candidate.writeByte,hk,Ptx.Event.Kind.writeByte] at hw

end
end Ptx.AmpereTiledGraph
