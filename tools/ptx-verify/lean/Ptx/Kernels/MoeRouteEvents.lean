import Ptx.Kernels.MoeRouteConfig

/-! Actual PC=0 source provenance, for arbitrary launch candidates and read
oracles. Each active token has exactly two gate reads and one u32 write. -/
namespace Ptx.MoeRouteEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeRouteThread
noncomputable section

def answer (oracle : Scalar.Oracle) : Nat := gtFlag (replyReal oracle 1) (replyReal oracle 0)
def eventsFor (cfg : Config) (id : ThreadId) (oracle : Scalar.Oracle) : List Scalar.Kind := [
  .read (gLoc cfg (index cfg id) 0) (Symbolic.encode .f32 (replyReal oracle 0)),
  .read (gLoc cfg (index cfg id) 1) (Symbolic.encode .f32 (replyReal oracle 1)),
  .write (rLoc cfg (index cfg id)) (u32Bytes (answer oracle))]

theorem trace_run {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hg : launch.geometry = cfg.geometry) (ht : t ∈ execution.traces) :
    ∃ floats, Scalar.run (context cfg launch.params t.id) t.oracle code t.count {} = .ok (⟨t.final,floats⟩,t.events) := by
  obtain ⟨floats,hr⟩ := (hw.2.2.1 t ht).2
  exact ⟨floats,by simpa only [hg,context] using hr⟩

theorem active_trace {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) : t.count = 22 ∧ t.events = eventsFor cfg t.id t.oracle := by
  have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
  obtain ⟨floats,hr⟩ := trace_run hw hg ht
  obtain ⟨a,b,h0,h1,hcount,he⟩ := reconstruct_active cfg.input (context cfg launch.params t.id) t.oracle hp
    (index_bounds cfg hv launch.params) ha (gate_end cfg ha) (route_end cfg ha) hr (hd t ht)
  refine ⟨hcount,?_⟩
  simpa only [eventsFor,answer,replyReal_of_typed h0,replyReal_of_typed h1,reads,context,index,g_zero,g_one,rLoc,
    List.cons_append,List.nil_append] using he

theorem trace_form {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) (ht : t ∈ execution.traces) :
    (t.count = 11 ∧ t.events = []) ∨ (Active cfg t.id ∧ t.count = 22 ∧ t.events = eventsFor cfg t.id t.oracle) := by
  by_cases ha : Active cfg t.id
  · exact .inr ⟨ha,active_trace hw hd hg hp ht ha⟩
  · have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
    obtain ⟨floats,hr⟩ := trace_run hw hg ht
    obtain ⟨hn,_,he⟩ := reconstruct_masked cfg.input (context cfg launch.params t.id) t.oracle hp
      (index_bounds cfg hv launch.params) (Nat.le_of_not_gt ha) hr (hd t ht)
    exact .inl ⟨hn,he⟩

theorem event_shape {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {kind : Scalar.Kind} (he : execution.eventAt event = some kind) :
    ∃ oracle : Scalar.Oracle, event.thread.Valid cfg.geometry ∧ Active cfg event.thread ∧
      ((event.serial = 0 ∧ kind = .read (gLoc cfg (index cfg event.thread) 0) (Symbolic.encode .f32 (replyReal oracle 0))) ∨
       (event.serial = 1 ∧ kind = .read (gLoc cfg (index cfg event.thread) 1) (Symbolic.encode .f32 (replyReal oracle 1))) ∨
       (event.serial = 2 ∧ kind = .write (rLoc cfg (index cfg event.thread)) (u32Bytes (answer oracle)))) := by
  obtain ⟨t,ht,htid,hindex⟩ := eventAt_trace he
  rcases event with ⟨thread,serial⟩
  simp only at htid
  subst thread
  have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
  rcases trace_form hw hd hg hp ht with ⟨_,hempty⟩ | ⟨ha,_,hshape⟩
  · simp [hempty] at hindex
  · refine ⟨t.oracle,hv,ha,?_⟩
    rw [hshape] at hindex
    have hb := (List.getElem?_eq_some_iff.mp hindex).1
    simp only [eventsFor,List.length_cons,List.length_nil] at hb
    rcases (show serial = 0 ∨ serial = 1 ∨ serial = 2 by omega) with rfl | rfl | rfl
    · exact .inl ⟨rfl,by simpa only [eventsFor,List.getElem?_cons_zero] using (Option.some.inj hindex).symm⟩
    · exact .inr (.inl ⟨rfl,by simpa only [eventsFor,List.getElem?_cons_succ,List.getElem?_cons_zero] using (Option.some.inj hindex).symm⟩)
    · exact .inr (.inr ⟨rfl,by simpa only [eventsFor,List.getElem?_cons_succ,List.getElem?_cons_zero] using (Option.some.inj hindex).symm⟩)

theorem read_region {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.readByte event loc = some value) :
    InWords cfg.input.g (2*cfg.input.m) loc := by
  cases he : execution.eventAt event with
  | none => simp [Candidate.readByte,he] at hr
  | some kind =>
    obtain ⟨oracle,hv,ha,hcases⟩ := event_shape hw hd hg hp he
    rcases hcases with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · apply encoded_in_region (gate_index_bound cfg ha (show (0 : Nat) < 2 by decide))
      simpa only [Candidate.readByte,he,Option.bind_some,Kind.readByte,gLoc] using hr
    · apply encoded_in_region (gate_index_bound cfg ha (show (1 : Nat) < 2 by decide))
      simpa only [Candidate.readByte,he,Option.bind_some,Kind.readByte,gLoc] using hr
    · simp [Candidate.readByte,he,Kind.readByte] at hr

theorem write_shape {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.writeByte event loc = some value) :
    event.thread.Valid cfg.geometry ∧ Active cfg event.thread ∧ event.serial = 2 ∧
      ∃ answer : Nat, payloadByte (rLoc cfg (index cfg event.thread)) (u32Bytes answer) loc = some value := by
  cases he : execution.eventAt event with
  | none => simp [Candidate.writeByte,he] at hr
  | some kind =>
    obtain ⟨oracle,hv,ha,hcases⟩ := event_shape hw hd hg hp he
    rcases hcases with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨hs,rfl⟩
    · simp [Candidate.writeByte,he,Kind.writeByte] at hr
    · simp [Candidate.writeByte,he,Kind.writeByte] at hr
    · exact ⟨hv,ha,hs,answer oracle,by simpa only [Candidate.writeByte,he,Option.bind_some,Kind.writeByte] using hr⟩

theorem write_region {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.writeByte event loc = some value) :
    InWords cfg.input.r cfg.input.m loc := by
  obtain ⟨_,ha,_,answer,hpayload⟩ := write_shape hw hd hg hp hr
  exact word_payload_in_region ha (u32_bytes_size answer) hpayload

theorem access_bounds {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {kind : Scalar.Kind} (he : execution.eventAt event = some kind) :
    ∃ base, kind.footprint = some (base,4) ∧ base.space = .global ∧
      base.address % 4 = 0 ∧ base.address+3 < 2^64 := by
  obtain ⟨oracle,hv,ha,hcases⟩ := event_shape hw hd hg hp he
  rcases hcases with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩
  · exact ⟨_,by simp [Kind.footprint,Symbolic.Format.bytes],rfl,gate_aligned cfg ha 0,gate_footprint cfg ha (by decide) (by decide)⟩
  · exact ⟨_,by simp [Kind.footprint,Symbolic.Format.bytes],rfl,gate_aligned cfg ha 1,gate_footprint cfg ha (by decide) (by decide)⟩
  · exact ⟨_,by simp [Kind.footprint,u32_bytes_size],rfl,route_aligned cfg ha,route_footprint cfg ha (by decide)⟩

end
end Ptx.MoeRouteEvent
