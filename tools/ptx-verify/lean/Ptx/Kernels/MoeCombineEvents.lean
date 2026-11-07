import Ptx.Kernels.MoeCombineConfig

/-! Actual complete-source gather events, including invalid-route candidates.
Route agreement is derived later, after input/output separation. -/
namespace Ptx.MoeCombineEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeCombine
noncomputable section

def routeValue (oracle : Scalar.Oracle) : Nat := match oracle 0 with | .integer value => value | _ => 0
def expert (oracle : Scalar.Oracle) : Nat := wrap 32 (routeValue oracle)
def answer (oracle : Scalar.Oracle) : ℝ := Scalar.replyReal oracle 1
def routeKind (cfg : Config) (id : ThreadId) (oracle : Scalar.Oracle) : Scalar.Kind :=
  .read (rLoc cfg (row cfg.geometry.block id)) (u32Bytes (expert oracle))
def eventsFor (cfg : Config) (id : ThreadId) (oracle : Scalar.Oracle) : List Scalar.Kind :=
  [routeKind cfg id oracle,
   .read (hLoc cfg (expert oracle) (row cfg.geometry.block id) (col cfg.geometry.block id)) (Symbolic.encode .f32 (answer oracle)),
   .write (yLoc cfg (row cfg.geometry.block id) (col cfg.geometry.block id)) (Symbolic.encode .f32 (answer oracle))]

theorem expert_bound (oracle : Scalar.Oracle) : expert oracle < 2^32 := Nat.mod_lt _ (by decide)
theorem trace_run {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hg : launch.geometry = cfg.geometry) (ht : t ∈ execution.traces) :
    ∃ floats, Scalar.run (context cfg launch.params t.id) t.oracle code t.count {} = .ok (⟨t.final,floats⟩,t.events) := by
  obtain ⟨floats,hr⟩ := (hw.2.2.1 t ht).2
  exact ⟨floats,by simpa only [hg,context] using hr⟩

theorem active_route_reply {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) : t.oracle 0 = .integer (routeValue t.oracle) := by
  have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
  obtain ⟨floats,hr⟩ := trace_run hw hg ht
  obtain ⟨value,hq⟩ := completed_route_reply cfg.input (context cfg launch.params t.id) t.oracle hp
    (index_bounds cfg hv launch.params) ha.1 ha.2 (route_pointer_bound cfg ha) hr (hd t ht)
  simpa only [routeValue,hq] using hq

theorem active_trace {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (he : expert t.oracle < 2) :
    t.events = eventsFor cfg t.id t.oracle := by
  have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
  obtain ⟨floats,hr⟩ := trace_run hw hg ht
  have hs := reconstruct_active cfg.input (context cfg launch.params t.id) t.oracle (routeValue t.oracle) hp
    (index_bounds cfg hv launch.params) ha.1 ha.2 (route_pointer_bound cfg ha)
    (active_route_reply hw hd hg hp ht ha) he (address_bounds cfg launch.params ha he) hr (hd t ht)
  simpa only [eventsFor,routeKind,rLoc,routeEvent,expert,answer,bodyEvents,hAddress,yAddress,
    context,h_address,hLoc,yLoc,List.singleton_append] using hs.2.2

theorem trace_form {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) (ht : t ∈ execution.traces) :
    t.events = [] ∨ ∃ ha : Active cfg t.id,
      t.events = [routeKind cfg t.id t.oracle] ∨ ∃ he : expert t.oracle < 2,
        t.events = eventsFor cfg t.id t.oracle := by
  have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
  obtain ⟨floats,hrun⟩ := trace_run hw hg ht
  by_cases hr : row cfg.geometry.block t.id < cfg.input.m
  · by_cases hc : col cfg.geometry.block t.id < cfg.input.n
    · have ha : Active cfg t.id := ⟨hr,hc⟩
      right; refine ⟨ha,?_⟩
      by_cases he : expert t.oracle < 2
      · exact .inr ⟨he,active_trace hw hd hg hp ht ha he⟩
      · obtain ⟨last,hex,hdone,_⟩ := invalid_route_execution cfg.input (context cfg launch.params t.id) t.oracle
          (routeValue t.oracle) hp (index_bounds cfg hv launch.params) hr hc (route_pointer_bound cfg ha)
          (active_route_reply hw hd hg hp ht ha) (Nat.le_of_not_gt he)
        have hs := (complete_run_unique hrun (hd t ht) hex hdone).2.2
        exact .inl (by simpa only [routeKind,routeEvent,rLoc,context,expert] using hs)
    · obtain ⟨last,hex,hdone,_⟩ := masked_col cfg.input (context cfg launch.params t.id) t.oracle hp
        (index_bounds cfg hv launch.params) hr (Nat.le_of_not_gt hc)
      exact .inl (complete_run_unique hrun (hd t ht) hex hdone).2.2
  · obtain ⟨last,hex,hdone,_⟩ := masked_row cfg.input (context cfg launch.params t.id) t.oracle hp
      (index_bounds cfg hv launch.params) (Nat.le_of_not_gt hr)
    exact .inl (complete_run_unique hrun (hd t ht) hex hdone).2.2

theorem event_shape {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {kind : Scalar.Kind} (hevent : execution.eventAt event = some kind) :
    ∃ oracle : Scalar.Oracle, event.thread.Valid cfg.geometry ∧ Active cfg event.thread ∧
      ((event.serial = 0 ∧ kind = routeKind cfg event.thread oracle) ∨
       (expert oracle < 2 ∧
        ((event.serial = 1 ∧ kind = .read (hLoc cfg (expert oracle) (row cfg.geometry.block event.thread) (col cfg.geometry.block event.thread))
          (Symbolic.encode .f32 (answer oracle))) ∨
         (event.serial = 2 ∧ kind = .write (yLoc cfg (row cfg.geometry.block event.thread) (col cfg.geometry.block event.thread))
          (Symbolic.encode .f32 (answer oracle)))))) := by
  obtain ⟨t,ht,htid,hindex⟩ := eventAt_trace hevent
  rcases event with ⟨thread,serial⟩
  simp only at htid
  subst thread
  have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
  rcases trace_form hw hd hg hp ht with hempty | ⟨ha,hsingle | ⟨he,hshape⟩⟩
  · simp [hempty] at hindex
  · rw [hsingle] at hindex
    have hb := (List.getElem?_eq_some_iff.mp hindex).1
    have hs : serial = 0 := by simp only [List.length_cons,List.length_nil] at hb; omega
    subst serial
    exact ⟨t.oracle,hv,ha,.inl ⟨rfl,(Option.some.inj hindex).symm⟩⟩
  · rw [hshape] at hindex
    have hb := (List.getElem?_eq_some_iff.mp hindex).1
    change serial < 3 at hb
    rcases (show serial = 0 ∨ serial = 1 ∨ serial = 2 by omega) with rfl | rfl | rfl
    · exact ⟨t.oracle,hv,ha,.inl ⟨rfl,(Option.some.inj hindex).symm⟩⟩
    · exact ⟨t.oracle,hv,ha,.inr ⟨he,.inl ⟨rfl,(Option.some.inj hindex).symm⟩⟩⟩
    · exact ⟨t.oracle,hv,ha,.inr ⟨he,.inr ⟨rfl,(Option.some.inj hindex).symm⟩⟩⟩

theorem read_region {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.readByte event loc = some value) :
    InWords cfg.input.r cfg.input.m loc ∨ InWords cfg.input.h ((2*cfg.input.m)*cfg.input.n) loc := by
  cases hevent : execution.eventAt event with
  | none => simp [Candidate.readByte,hevent] at hr
  | some kind =>
    obtain ⟨oracle,_,ha,hcases⟩ := event_shape hw hd hg hp hevent
    rcases hcases with ⟨_,rfl⟩ | ⟨he,⟨_,rfl⟩ | ⟨_,rfl⟩⟩
    · left
      apply word_payload_in_region ha.1 (u32_bytes_size (expert oracle))
      simpa only [Candidate.readByte,hevent,Option.bind_some,routeKind,Kind.readByte,rLoc] using hr
    · right
      apply encoded_in_region (h_index_bound cfg he ha.1 ha.2)
      simpa only [Candidate.readByte,hevent,Option.bind_some,Kind.readByte,hLoc] using hr
    · simp [Candidate.readByte,hevent,Kind.readByte] at hr

theorem write_shape {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.writeByte event loc = some value) :
    event.thread.Valid cfg.geometry ∧ Active cfg event.thread ∧ event.serial = 2 ∧
      ∃ answer : ℝ, payloadByte (yLoc cfg (row cfg.geometry.block event.thread) (col cfg.geometry.block event.thread))
        (Symbolic.encode .f32 answer) loc = some value := by
  cases hevent : execution.eventAt event with
  | none => simp [Candidate.writeByte,hevent] at hr
  | some kind =>
    obtain ⟨oracle,hv,ha,hcases⟩ := event_shape hw hd hg hp hevent
    rcases hcases with ⟨_,rfl⟩ | ⟨_,⟨_,rfl⟩ | ⟨hs,rfl⟩⟩
    · simp [Candidate.writeByte,hevent,routeKind,Kind.writeByte] at hr
    · simp [Candidate.writeByte,hevent,Kind.writeByte] at hr
    · exact ⟨hv,ha,hs,answer oracle,
        by simpa only [Candidate.writeByte,hevent,Option.bind_some,Kind.writeByte] using hr⟩

theorem write_region {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.writeByte event loc = some value) :
    InWords cfg.input.y (cfg.input.m*cfg.input.n) loc := by
  obtain ⟨_,ha,_,value,hpayload⟩ := write_shape hw hd hg hp hr
  exact encoded_in_region (y_index_bound cfg ha.1 ha.2) hpayload

theorem access_bounds {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {kind : Scalar.Kind} (hevent : execution.eventAt event = some kind) :
    ∃ base, kind.footprint = some (base,4) ∧ base.space = .global ∧
      base.address % 4 = 0 ∧ base.address+3 < 2^64 := by
  obtain ⟨oracle,_,ha,hcases⟩ := event_shape hw hd hg hp hevent
  rcases hcases with ⟨_,rfl⟩ | ⟨hexpert,⟨_,rfl⟩ | ⟨_,rfl⟩⟩
  · exact ⟨_,by simp [routeKind,Kind.footprint,u32_bytes_size],rfl,
      r_aligned cfg ha.1 (by have := ha.2; omega),r_footprint cfg ha.1 (by have := ha.2; omega) (by decide)⟩
  · exact ⟨_,by simp [Kind.footprint,Symbolic.Format.bytes],rfl,
      h_aligned cfg ha.1 ha.2,h_footprint cfg hexpert ha.1 ha.2 (by decide)⟩
  · exact ⟨_,by simp [Kind.footprint,Symbolic.Format.bytes],rfl,
      y_aligned cfg ha.1 ha.2,y_footprint cfg ha.1 ha.2 (by decide)⟩

end
end Ptx.MoeCombineEvent
