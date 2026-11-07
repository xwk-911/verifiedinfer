import Ptx.Kernels.ScalarAttentionConfig
import Ptx.Kernels.ScalarAttentionReadEvents

/-! Launch-wide provenance of every event emitted by the actual attention
source. Completion counts, thread oracles and the order of traces remain free.
The reconstructed reply values are not assumed to equal initialized inputs. -/
namespace Ptx.ScalarAttentionEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.ScalarAttention Ptx.ScalarAttentionInit
noncomputable section

def layout (cfg : Config) (params : Bindings) (id : ThreadId) (ha : Active cfg id) (hn : 0 < cfg.input.n) :=
  threadLayout cfg.input (context cfg params id) (address_bounds cfg params ha hn)

def answer (cfg : Config) (params : Bindings) (id : ThreadId) (oracle : Scalar.Oracle) (ha : Active cfg id) : ℝ :=
  if hn : 0 < cfg.input.n then
    OnlineSoftmax.average (ScalarAttentionTrace.scores (layout cfg params id ha hn) oracle (replyReal oracle 0))
      (ScalarAttentionTrace.values (layout cfg params id ha hn) oracle) cfg.input.n
  else 0

def readEventsFor (cfg : Config) (params : Bindings) (id : ThreadId) (oracle : Scalar.Oracle) (ha : Active cfg id) : List Scalar.Kind :=
  if hn : 0 < cfg.input.n then
    [.read (scaleLoc cfg) (Symbolic.encode .f32 (replyReal oracle 0))] ++
      ScalarAttentionReads.reads (layout cfg params id ha hn)
        (ScalarAttentionTrace.qValues (layout cfg params id ha hn) oracle)
        (ScalarAttentionTrace.keyValues (layout cfg params id ha hn) oracle)
        (ScalarAttentionTrace.values (layout cfg params id ha hn) oracle) 0 cfg.input.n
  else []

def eventsFor (cfg : Config) (params : Bindings) (id : ThreadId) (oracle : Scalar.Oracle) (ha : Active cfg id) : List Scalar.Kind :=
  readEventsFor cfg params id oracle ha ++
    [.write (outputLoc cfg (row cfg.geometry.block id) (col cfg.geometry.block id))
      (Symbolic.encode .f32 (answer cfg params id oracle ha))]

def writeSerial (cfg : Config) : Nat := if cfg.input.n = 0 then 0 else 1+(2*cfg.input.dim+1)*cfg.input.n

@[simp] theorem readEventsFor_length (cfg : Config) (params : Bindings) (id : ThreadId)
    (oracle : Scalar.Oracle) (ha : Active cfg id) : (readEventsFor cfg params id oracle ha).length = writeSerial cfg := by
  by_cases hn : 0 < cfg.input.n
  · simp [readEventsFor,hn,writeSerial,hn.ne',ScalarAttentionReads.reads_length,layout,threadLayout,Nat.add_comm]
  · have hz : cfg.input.n = 0 := by omega
    simp [readEventsFor,writeSerial,hz]

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
  by_cases hn : 0 < cfg.input.n
  · obtain ⟨scale,hs,_,hev⟩ := active_completed_shape cfg.input (context cfg launch.params t.id) t.oracle hp
      (index_bounds cfg hv launch.params) ha.1 ha.2 hn (address_bounds cfg launch.params ha hn) hr (hd t ht)
    have hscale := replyReal_of_typed hs
    simpa only [eventsFor,readEventsFor,answer,dite_eq_left hn,layout,scaleLoc,outputLoc,
      context,outputAddress,hscale,List.append_assoc] using hev
  · have hz : cfg.input.n = 0 := by omega
    obtain ⟨_,hev⟩ := empty_completed_shape cfg.input (context cfg launch.params t.id) t.oracle hp
      (index_bounds cfg hv launch.params) ha.1 ha.2 hz (output_bound cfg launch.params ha) hr (hd t ht)
    simpa only [eventsFor,readEventsFor,answer,dite_eq_right hn,List.nil_append,outputLoc,context,outputAddress] using hev

theorem trace_form {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) (ht : t ∈ execution.traces) :
    t.events = [] ∨ ∃ ha : Active cfg t.id, t.events = eventsFor cfg launch.params t.id t.oracle ha := by
  by_cases ha : Active cfg t.id
  · exact .inr ⟨ha,active_trace hw hd hg hp ht ha⟩
  · have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
    obtain ⟨floats,hr⟩ := trace_run hw hg ht
    have hs := completed_source_cases cfg.input (context cfg launch.params t.id) t.oracle hp
      (index_bounds cfg hv launch.params)
      (fun hrow hcol => output_bound cfg launch.params ⟨hrow,hcol⟩)
      (fun hrow hcol hn => address_bounds cfg launch.params ⟨hrow,hcol⟩ hn) hr (hd t ht)
    rcases hs with ⟨_,_,he⟩ | ⟨_,_,_,he⟩ | ⟨hrow,hcol,_,_,_⟩ | ⟨hrow,hcol,_,_⟩
    · exact .inl he
    · exact .inl he
    · exact (ha ⟨hrow,hcol⟩).elim
    · exact (ha ⟨hrow,hcol⟩).elim

theorem layout_q (cfg : Config) (params : Bindings) {id : ThreadId} (ha : Active cfg id)
    (hn : 0 < cfg.input.n) (k : Nat) :
    (⟨.global,(layout cfg params id ha hn).qBase+4*k⟩ : Location) = qLoc cfg (row cfg.geometry.block id) k := by
  simp only [layout,threadLayout,context,qLoc,Nat.mul_add,Nat.add_assoc]

theorem layout_key (cfg : Config) (params : Bindings) {id : ThreadId} (ha : Active cfg id)
    (hn : 0 < cfg.input.n) (j k : Nat) :
    (⟨.global,(layout cfg params id ha hn).keyBase+4*(layout cfg params id ha hn).dim*j+4*k⟩ : Location) = keyLoc cfg j k := by
  simp only [layout,threadLayout,keyLoc,Nat.mul_assoc,Nat.mul_comm cfg.input.dim j,Nat.mul_add,Nat.add_assoc]

theorem layout_value (cfg : Config) (params : Bindings) {id : ThreadId} (ha : Active cfg id)
    (hn : 0 < cfg.input.n) (j : Nat) :
    (⟨.global,(layout cfg params id ha hn).valueBase+4*(layout cfg params id ha hn).dim*j⟩ : Location) =
      valueLoc cfg j (col cfg.geometry.block id) := by
  simp only [layout,threadLayout,context,valueLoc,Nat.mul_assoc,Nat.mul_comm cfg.input.dim j,Nat.mul_add]
  congr 1
  omega

def ReadFrom (cfg : Config) (id : ThreadId) (loc : Location) : Prop :=
  loc = scaleLoc cfg ∨
  (∃ k, k < cfg.input.dim ∧ loc = qLoc cfg (row cfg.geometry.block id) k) ∨
  (∃ j k, j < cfg.input.n ∧ k < cfg.input.dim ∧ loc = keyLoc cfg j k) ∨
  (∃ j, j < cfg.input.n ∧ loc = valueLoc cfg j (col cfg.geometry.block id))

theorem readEventsFor_event {cfg : Config} {params : Bindings} {id : ThreadId} {oracle : Scalar.Oracle}
    {ha : Active cfg id} {serial : Nat} {kind : Scalar.Kind}
    (he : (readEventsFor cfg params id oracle ha)[serial]? = some kind) :
    ReadsEnabled cfg.input ∧ ∃ base value, ReadFrom cfg id base ∧ kind = .read base (Symbolic.encode .f32 value) := by
  by_cases hn : 0 < cfg.input.n
  · refine ⟨reads_enabled ha hn,?_⟩
    rw [readEventsFor,dite_eq_left hn] at he
    cases serial with
    | zero =>
      simp only [List.cons_append,List.nil_append,List.getElem?_cons_zero] at he
      exact ⟨_,_,.inl rfl,(Option.some.inj he).symm⟩
    | succ serial =>
      simp only [List.cons_append,List.nil_append,List.getElem?_cons_succ] at he
      obtain ⟨j,_,_,hj,hkind⟩ := ScalarAttentionReads.reads_event (by simp [layout,threadLayout]) he
      rcases hkind with ⟨k,hk,rfl⟩ | ⟨k,hk,rfl⟩ | rfl
      · exact ⟨_,_,.inr (.inl ⟨k,hk,layout_q cfg params ha hn k⟩),rfl⟩
      · exact ⟨_,_,.inr (.inr (.inl ⟨j,k,hj,hk,layout_key cfg params ha hn j k⟩)),rfl⟩
      · exact ⟨_,_,.inr (.inr (.inr ⟨j,hj,layout_value cfg params ha hn j⟩)),rfl⟩
  · simp [readEventsFor,hn] at he

theorem event_shape {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {kind : Scalar.Kind} (he : execution.eventAt event = some kind) :
    ∃ oracle : Scalar.Oracle, event.thread.Valid cfg.geometry ∧ ∃ ha : Active cfg event.thread,
      ((ReadsEnabled cfg.input ∧ ∃ base value, ReadFrom cfg event.thread base ∧ kind = .read base (Symbolic.encode .f32 value)) ∨
       (event.serial = writeSerial cfg ∧ kind =
          .write (outputLoc cfg (row cfg.geometry.block event.thread) (col cfg.geometry.block event.thread))
            (Symbolic.encode .f32 (answer cfg launch.params event.thread oracle ha)))) := by
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
    simp only [eventsFor,List.length_append,readEventsFor_length,List.length_cons,List.length_nil] at hb
    unfold eventsFor at hindex
    by_cases hr : serial < writeSerial cfg
    · rw [List.getElem?_append_left (by simpa only [readEventsFor_length] using hr)] at hindex
      exact .inl (readEventsFor_event hindex)
    · have hs : serial = writeSerial cfg := by omega
      subst serial
      rw [List.getElem?_append_right (by simp)] at hindex
      simp only [readEventsFor_length,Nat.sub_self,List.getElem?_cons_zero] at hindex
      exact .inr ⟨rfl,(Option.some.inj hindex).symm⟩

def InInput (cfg : Config) (loc : Location) : Prop := ReadsEnabled cfg.input ∧
  (InWords cfg.input.scale 1 loc ∨ InWords cfg.input.q (cfg.input.m*cfg.input.dim) loc ∨
   InWords cfg.input.key (cfg.input.n*cfg.input.dim) loc ∨ InWords cfg.input.value (cfg.input.n*cfg.input.dim) loc)

theorem read_location_bounds (cfg : Config) {id : ThreadId} (ha : Active cfg id)
    (he : ReadsEnabled cfg.input) {loc : Location} (hr : ReadFrom cfg id loc) :
    loc.space = .global ∧ loc.address % 4 = 0 ∧ loc.address+3 < 2^64 := by
  rcases hr with rfl | ⟨k,hk,rfl⟩ | ⟨j,k,hj,hk,rfl⟩ | ⟨j,hj,rfl⟩
  · exact ⟨rfl,scale_aligned cfg he,scale_footprint cfg he (by decide)⟩
  · exact ⟨rfl,q_aligned cfg he _ _,q_footprint cfg he ha.1 hk (by decide)⟩
  · exact ⟨rfl,key_aligned cfg he _ _,key_footprint cfg he hj hk (by decide)⟩
  · exact ⟨rfl,value_aligned cfg he _ _,value_footprint cfg he hj ha.2 (by decide)⟩

theorem access_bounds {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {kind : Scalar.Kind} (he : execution.eventAt event = some kind) :
    ∃ base value, (kind = .read base (Symbolic.encode .f32 value) ∨ kind = .write base (Symbolic.encode .f32 value)) ∧
      base.space = .global ∧ base.address % 4 = 0 ∧ base.address+3 < 2^64 := by
  obtain ⟨oracle,hv,ha,hs⟩ := event_shape hw hd hg hp he
  rcases hs with ⟨hen,base,value,hr,rfl⟩ | ⟨_,rfl⟩
  · exact ⟨base,value,.inl rfl,read_location_bounds cfg ha hen hr⟩
  · exact ⟨_,_,.inr rfl,rfl,output_aligned cfg ha.1 ha.2,output_footprint cfg ha.1 ha.2 (by decide)⟩

theorem read_region {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.readByte event loc = some value) :
    InInput cfg loc := by
  cases he : execution.eventAt event with
  | none => simp [Candidate.readByte,he] at hr
  | some kind =>
    obtain ⟨oracle,hv,ha,hs⟩ := event_shape hw hd hg hp he
    rcases hs with ⟨hen,base,x,hfrom,rfl⟩ | ⟨_,rfl⟩
    · refine ⟨hen,?_⟩
      have hpayload : payloadByte base (Symbolic.encode .f32 x) loc = some value := by
        simpa only [Candidate.readByte,he,Option.bind_some,Kind.readByte] using hr
      rcases hfrom with rfl | ⟨k,hk,rfl⟩ | ⟨j,k,hj,hk,rfl⟩ | ⟨j,hj,rfl⟩
      · exact .inl (encoded_in_region (index := 0) (by decide) (by simpa only [scaleLoc,Nat.mul_zero,Nat.add_zero] using hpayload))
      · exact .inr (.inl (encoded_in_region (q_index_bound cfg ha.1 hk) hpayload))
      · exact .inr (.inr (.inl (encoded_in_region (key_index_bound cfg hj hk) hpayload)))
      · exact .inr (.inr (.inr (encoded_in_region (key_index_bound cfg hj ha.2) hpayload)))
    · simp [Candidate.readByte,he,Kind.readByte] at hr

theorem write_shape {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.writeByte event loc = some value) :
    event.thread.Valid cfg.geometry ∧ Active cfg event.thread ∧ event.serial = writeSerial cfg ∧
      ∃ x : ℝ, payloadByte (outputLoc cfg (row cfg.geometry.block event.thread) (col cfg.geometry.block event.thread))
        (Symbolic.encode .f32 x) loc = some value := by
  cases he : execution.eventAt event with
  | none => simp [Candidate.writeByte,he] at hr
  | some kind =>
    obtain ⟨oracle,hv,ha,hs⟩ := event_shape hw hd hg hp he
    rcases hs with ⟨_,base,x,_,rfl⟩ | ⟨hs,rfl⟩
    · simp [Candidate.writeByte,he,Kind.writeByte] at hr
    · exact ⟨hv,ha,hs,answer cfg launch.params event.thread oracle ha,
        by simpa only [Candidate.writeByte,he,Option.bind_some,Kind.writeByte] using hr⟩

theorem write_region {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.writeByte event loc = some value) :
    InWords cfg.input.output (cfg.input.m*cfg.input.dim) loc := by
  obtain ⟨_,ha,_,x,hpayload⟩ := write_shape hw hd hg hp hr
  exact encoded_in_region (output_index_bound cfg ha.1 ha.2) hpayload

end
end Ptx.ScalarAttentionEvent
