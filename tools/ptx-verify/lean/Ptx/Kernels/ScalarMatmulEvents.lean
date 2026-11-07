import Ptx.Kernels.ScalarMatmulConfig

/-! Launch-wide event provenance for the mechanically translated matrix source.
No input oracle, memory witness or trace-list order is selected by these facts.
-/
namespace Ptx.ScalarMatmulEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarMatmul Ptx.ScalarMatmulInit Ptx.ScalarMatmulLoop
noncomputable section

def answer (cfg : Config) (oracle : Scalar.Oracle) : ℝ := prefixProduct (replyA oracle) (replyB oracle) 0 0 cfg.input.k
def eventsFor (cfg : Config) (params : Bindings) (id : ThreadId) (oracle : Scalar.Oracle) (ha : Active cfg id) : List Scalar.Kind :=
  loopReads (threadLayout cfg.input (context cfg params id) (address_bounds cfg params ha))
    (replyA oracle) (replyB oracle) 0 0 0 cfg.input.k ++
    [.write (cLoc cfg (row cfg.geometry.block id) (col cfg.geometry.block id)) (Symbolic.encode .f32 (answer cfg oracle))]

theorem trace_run {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hg : launch.geometry = cfg.geometry) (ht : t ∈ execution.traces) :
    ∃ floats, Scalar.run (context cfg launch.params t.id) t.oracle code t.count {} = .ok (⟨t.final,floats⟩,t.events) := by
  obtain ⟨floats,hr⟩ := (hw.2.2.1 t ht).2
  exact ⟨floats,by simpa only [hg,context] using hr⟩

theorem active_trace {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) : t.events = eventsFor cfg launch.params t.id t.oracle ha := by
  have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
  obtain ⟨floats,hr⟩ := trace_run hw hg ht
  have hs := active_completed_shape cfg.input (context cfg launch.params t.id) t.oracle hp
    (index_bounds cfg hv launch.params) ha.1 ha.2 (address_bounds cfg launch.params ha) hr (hd t ht)
  simpa only [eventsFor,answer,context,cLoc,threadLayout] using hs.2

theorem trace_form {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) (ht : t ∈ execution.traces) :
    t.events = [] ∨ ∃ ha : Active cfg t.id, t.events = eventsFor cfg launch.params t.id t.oracle ha := by
  by_cases ha : Active cfg t.id
  · exact .inr ⟨ha,active_trace hw hd hg hp ht ha⟩
  · have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
    obtain ⟨floats,hr⟩ := trace_run hw hg ht
    have hs := completed_source_cases cfg.input (context cfg launch.params t.id) t.oracle hp
      (index_bounds cfg hv launch.params) (fun hrow hcol => address_bounds cfg launch.params ⟨hrow,hcol⟩) hr (hd t ht)
    rcases hs with ⟨_,_,he⟩ | ⟨_,_,_,he⟩ | ⟨hrow,hcol,_,_⟩
    · exact .inl he
    · exact .inl he
    · exact (ha ⟨hrow,hcol⟩).elim

theorem layout_a (cfg : Config) (params : Bindings) {id : ThreadId} (ha : Active cfg id) (k : Nat) :
    (⟨.global,(threadLayout cfg.input (context cfg params id) (address_bounds cfg params ha)).aBase+4*k⟩ : Location) =
      aLoc cfg (row cfg.geometry.block id) k := by
  change (⟨.global,cfg.input.a+4*(row cfg.geometry.block id*cfg.input.k)+4*k⟩ : Location) = _
  simp only [aLoc,Nat.mul_add,Nat.add_assoc]

theorem layout_b (cfg : Config) (params : Bindings) {id : ThreadId} (ha : Active cfg id) (k : Nat) :
    (⟨.global,(threadLayout cfg.input (context cfg params id) (address_bounds cfg params ha)).bBase+
      (threadLayout cfg.input (context cfg params id) (address_bounds cfg params ha)).stride*k⟩ : Location) =
      bLoc cfg k (col cfg.geometry.block id) := by
  change (⟨.global,cfg.input.b+4*col cfg.geometry.block id+(4*cfg.input.n)*k⟩ : Location) = _
  simp only [bLoc,Nat.mul_assoc]
  rw [Nat.mul_comm cfg.input.n k,Nat.mul_add]
  congr 1
  omega

theorem event_shape {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {kind : Scalar.Kind} (he : execution.eventAt event = some kind) :
    ∃ oracle : Scalar.Oracle, event.thread.Valid cfg.geometry ∧ Active cfg event.thread ∧
      ((∃ k, k < cfg.input.k ∧ event.serial = 2*k ∧ kind =
          .read (aLoc cfg (row cfg.geometry.block event.thread) k) (Symbolic.encode .f32 (realReply oracle (2*k)))) ∨
       (∃ k, k < cfg.input.k ∧ event.serial = 2*k+1 ∧ kind =
          .read (bLoc cfg k (col cfg.geometry.block event.thread)) (Symbolic.encode .f32 (realReply oracle (2*k+1)))) ∨
       (event.serial = 2*cfg.input.k ∧ kind =
          .write (cLoc cfg (row cfg.geometry.block event.thread) (col cfg.geometry.block event.thread))
            (Symbolic.encode .f32 (answer cfg oracle)))) := by
  obtain ⟨t,ht,htid,hindex⟩ := eventAt_trace he
  rcases event with ⟨thread,serial⟩
  simp only at htid
  subst thread
  have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
  rcases trace_form hw hd hg hp ht with hempty | ⟨ha,hshape⟩
  · simp [hempty] at hindex
  · refine ⟨t.oracle,hv,ha,?_⟩
    rw [hshape] at hindex
    have hb := (List.getElem?_eq_some_iff.mp hindex).1
    simp only [eventsFor,List.length_append,loopReads_length,List.length_cons,List.length_nil] at hb
    unfold eventsFor at hindex
    by_cases hr : serial < 2*cfg.input.k
    · rw [List.getElem?_append_left (by simpa only [loopReads_length] using hr)] at hindex
      obtain ⟨k,hk,hcases⟩ := loopReads_event hindex
      rcases hcases with ⟨hs,hkind⟩ | ⟨hs,hkind⟩
      · left
        exact ⟨k,hk,hs,by simpa only [replyA,Nat.zero_add,layout_a cfg launch.params ha k] using hkind⟩
      · right; left
        exact ⟨k,hk,hs,by simpa only [replyB,Nat.zero_add,layout_b cfg launch.params ha k] using hkind⟩
    · have hs : serial = 2*cfg.input.k := by omega
      subst serial
      rw [List.getElem?_append_right (by simp)] at hindex
      simp only [loopReads_length,Nat.sub_self,List.getElem?_cons_zero] at hindex
      exact .inr (.inr ⟨rfl,(Option.some.inj hindex).symm⟩)

theorem read_region {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.readByte event loc = some value) :
    InWords cfg.input.a (cfg.input.m*cfg.input.k) loc ∨ InWords cfg.input.b (cfg.input.k*cfg.input.n) loc := by
  cases he : execution.eventAt event with
  | none => simp [Candidate.readByte,he] at hr
  | some kind =>
    obtain ⟨oracle,hv,ha,hcases⟩ := event_shape hw hd hg hp he
    rcases hcases with ⟨k,hk,_,rfl⟩ | ⟨k,hk,_,rfl⟩ | ⟨_,rfl⟩
    · left
      apply encoded_in_region (a_index_bound cfg ha.1 hk)
      simpa only [Candidate.readByte,he,Option.bind_some,Kind.readByte,aLoc] using hr
    · right
      apply encoded_in_region (b_index_bound cfg hk ha.2)
      simpa only [Candidate.readByte,he,Option.bind_some,Kind.readByte,bLoc] using hr
    · simp [Candidate.readByte,he,Kind.readByte] at hr

theorem write_shape {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.writeByte event loc = some value) :
    event.thread.Valid cfg.geometry ∧ Active cfg event.thread ∧ event.serial = 2*cfg.input.k ∧
      ∃ answer : ℝ, payloadByte (cLoc cfg (row cfg.geometry.block event.thread) (col cfg.geometry.block event.thread))
        (Symbolic.encode .f32 answer) loc = some value := by
  cases he : execution.eventAt event with
  | none => simp [Candidate.writeByte,he] at hr
  | some kind =>
    obtain ⟨oracle,hv,ha,hcases⟩ := event_shape hw hd hg hp he
    rcases hcases with ⟨_,_,_,rfl⟩ | ⟨_,_,_,rfl⟩ | ⟨hs,rfl⟩
    · simp [Candidate.writeByte,he,Kind.writeByte] at hr
    · simp [Candidate.writeByte,he,Kind.writeByte] at hr
    · exact ⟨hv,ha,hs,answer cfg oracle,by simpa only [Candidate.writeByte,he,Option.bind_some,Kind.writeByte] using hr⟩

theorem write_region {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.writeByte event loc = some value) :
    InWords cfg.input.c (cfg.input.m*cfg.input.n) loc := by
  obtain ⟨_,ha,_,answer,hpayload⟩ := write_shape hw hd hg hp hr
  exact encoded_in_region (c_index_bound cfg ha.1 ha.2) hpayload

theorem access_bounds {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {kind : Scalar.Kind} (he : execution.eventAt event = some kind) :
    ∃ base value, (kind = .read base (Symbolic.encode .f32 value) ∨ kind = .write base (Symbolic.encode .f32 value)) ∧
      base.space = .global ∧ base.address % 4 = 0 ∧ base.address+3 < 2^64 := by
  obtain ⟨oracle,hv,ha,hcases⟩ := event_shape hw hd hg hp he
  rcases hcases with ⟨k,hk,_,rfl⟩ | ⟨k,hk,_,rfl⟩ | ⟨_,rfl⟩
  · exact ⟨_,_,.inl rfl,rfl,a_aligned cfg _ _,a_footprint cfg ha.1 hk (by decide)⟩
  · exact ⟨_,_,.inl rfl,rfl,b_aligned cfg _ _,b_footprint cfg hk ha.2 (by decide)⟩
  · exact ⟨_,_,.inr rfl,rfl,c_aligned cfg _ _,c_footprint cfg ha.1 ha.2 (by decide)⟩

end
end Ptx.ScalarMatmulEvent
