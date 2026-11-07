import Ptx.Kernels.MoeExpertsConfig

/-! Actual launch-wide source events before gate/route agreement is known.
Invalid route candidates still read R and must participate in the memory proof. -/
namespace Ptx.MoeExpertsEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.MoeExperts Ptx.MoeExpertsLoop
noncomputable section

def routeValue (oracle : Scalar.Oracle) : Nat := match oracle 0 with | .integer value => value | _ => 0
def expert (oracle : Scalar.Oracle) : Nat := wrap 32 (routeValue oracle)
def answer (cfg : Config) (oracle : Scalar.Oracle) : ℝ :=
  ScalarMatmul.prefixProduct (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 cfg.input.k
def routeKind (cfg : Config) (id : ThreadId) (oracle : Scalar.Oracle) : Scalar.Kind :=
  .read (rLoc cfg (row cfg.geometry.block id)) (u32Bytes (expert oracle))
def eventsFor (cfg : Config) (params : Bindings) (id : ThreadId) (oracle : Scalar.Oracle)
    (ha : Active cfg id) (he : expert oracle < 2) : List Scalar.Kind :=
  routeKind cfg id oracle ::
    (FmaLoop.loopReads (threadLayout cfg.input (context cfg params id) (expert oracle) (address_bounds cfg params ha he))
      (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 0 cfg.input.k ++
      [.write (hLoc cfg (expert oracle) (row cfg.geometry.block id) (col cfg.geometry.block id)) (Symbolic.encode .f32 (answer cfg oracle))])

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

theorem layout_x (cfg : Config) (params : Bindings) {id : ThreadId} (ha : Active cfg id) {e : Nat} (he : e < 2) (k : Nat) :
    (⟨.global,(threadLayout cfg.input (context cfg params id) e (address_bounds cfg params ha he)).aBase+4*k⟩ : Location) =
      xLoc cfg (row cfg.geometry.block id) k := by
  simp only [threadLayout,context,xLoc,Nat.mul_add,Nat.add_assoc]
theorem layout_w (cfg : Config) (params : Bindings) {id : ThreadId} (ha : Active cfg id) {e : Nat} (he : e < 2) (k : Nat) :
    (⟨.global,(threadLayout cfg.input (context cfg params id) e (address_bounds cfg params ha he)).bBase+
      (threadLayout cfg.input (context cfg params id) e (address_bounds cfg params ha he)).stride*k⟩ : Location) =
      wLoc cfg e k (col cfg.geometry.block id) := by
  exact congrArg (Location.mk .global) (w_address _ _ _ _)
theorem layout_h (cfg : Config) (params : Bindings) {id : ThreadId} (ha : Active cfg id) {e : Nat} (he : e < 2) :
    (⟨.global,(threadLayout cfg.input (context cfg params id) e (address_bounds cfg params ha he)).output⟩ : Location) =
      hLoc cfg e (row cfg.geometry.block id) (col cfg.geometry.block id) := by
  exact congrArg (Location.mk .global) (h_address _ _ _ _)

theorem active_trace {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    (ht : t ∈ execution.traces) (ha : Active cfg t.id) (he : expert t.oracle < 2) :
    t.events = eventsFor cfg launch.params t.id t.oracle ha he := by
  have hv : t.id.Valid cfg.geometry := by simpa only [hg] using (hw.2.2.1 t ht).1
  obtain ⟨floats,hr⟩ := trace_run hw hg ht
  have hq := active_route_reply hw hd hg hp ht ha
  have hs := reconstruct_active cfg.input (context cfg launch.params t.id) t.oracle (routeValue t.oracle) hp
    (index_bounds cfg hv launch.params) ha.1 ha.2 (route_pointer_bound cfg ha) hq he
    (address_bounds cfg launch.params ha he) hr (hd t ht)
  have hloc := layout_h cfg launch.params ha (e := wrap 32 (routeValue t.oracle)) he
  rw [hloc] at hs
  simpa only [eventsFor,routeKind,rLoc,routeEvent,expert,answer,context,List.singleton_append,
    layout_h cfg launch.params ha he] using hs.2

theorem trace_form {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate} {t : Scalar.ThreadTrace}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params) (ht : t ∈ execution.traces) :
    t.events = [] ∨ ∃ ha : Active cfg t.id,
      t.events = [routeKind cfg t.id t.oracle] ∨ ∃ he : expert t.oracle < 2,
        t.events = eventsFor cfg launch.params t.id t.oracle ha he := by
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
        ((∃ k, k < cfg.input.k ∧ event.serial = 1+2*k ∧ kind =
            .read (xLoc cfg (row cfg.geometry.block event.thread) k) (Symbolic.encode .f32 (FmaLoop.realReply oracle (1+2*k)))) ∨
         (∃ k, k < cfg.input.k ∧ event.serial = 1+(2*k+1) ∧ kind =
            .read (wLoc cfg (expert oracle) k (col cfg.geometry.block event.thread)) (Symbolic.encode .f32 (FmaLoop.realReply oracle (1+2*k+1)))) ∨
         (event.serial = 1+2*cfg.input.k ∧ kind =
            .write (hLoc cfg (expert oracle) (row cfg.geometry.block event.thread) (col cfg.geometry.block event.thread))
              (Symbolic.encode .f32 (answer cfg oracle)))))) := by
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
  · refine ⟨t.oracle,hv,ha,?_⟩
    rw [hshape] at hindex
    by_cases hz : serial = 0
    · subst serial
      exact .inl ⟨rfl,(Option.some.inj hindex).symm⟩
    · right; refine ⟨he,?_⟩
      have hb := (List.getElem?_eq_some_iff.mp hindex).1
      simp only [eventsFor,List.length_cons,List.length_append,FmaLoop.loopReads_length,List.length_nil] at hb
      have hserial : serial = (serial-1)+1 := by omega
      rw [hserial] at hindex
      simp only [eventsFor,List.getElem?_cons_succ] at hindex
      by_cases hr : serial-1 < 2*cfg.input.k
      · rw [List.getElem?_append_left (by simpa only [FmaLoop.loopReads_length] using hr)] at hindex
        obtain ⟨k,hk,hcases⟩ := FmaLoop.loopReads_event hindex
        rcases hcases with ⟨hs,hkind⟩ | ⟨hs,hkind⟩
        · exact .inl ⟨k,hk,by change serial = 1+2*k; omega,by simpa only [Nat.zero_add,FmaLoop.replyA,layout_x cfg launch.params ha he k] using hkind⟩
        · exact .inr (.inl ⟨k,hk,by change serial = 1+(2*k+1); omega,by simpa only [Nat.zero_add,FmaLoop.replyB,layout_w cfg launch.params ha he k] using hkind⟩)
      · have hs : serial-1 = 2*cfg.input.k := by omega
        rw [List.getElem?_append_right (by simpa only [FmaLoop.loopReads_length] using Nat.le_of_not_gt hr)] at hindex
        simp only [FmaLoop.loopReads_length,hs,Nat.sub_self,List.getElem?_cons_zero] at hindex
        exact .inr (.inr ⟨by change serial = 1+2*cfg.input.k; omega,(Option.some.inj hindex).symm⟩)


theorem read_region {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.readByte event loc = some value) :
    InWords cfg.input.r cfg.input.m loc ∨ InWords cfg.input.x (cfg.input.m*cfg.input.k) loc ∨
      InWords cfg.input.w ((2*cfg.input.k)*cfg.input.n) loc := by
  cases hevent : execution.eventAt event with
  | none => simp [Candidate.readByte,hevent] at hr
  | some kind =>
    obtain ⟨oracle,hv,ha,hcases⟩ := event_shape hw hd hg hp hevent
    rcases hcases with ⟨_,rfl⟩ | ⟨he,⟨k,hk,_,rfl⟩ | ⟨k,hk,_,rfl⟩ | ⟨_,rfl⟩⟩
    · left
      apply word_payload_in_region ha.1 (u32_bytes_size (expert oracle))
      simpa only [Candidate.readByte,hevent,Option.bind_some,routeKind,Kind.readByte,rLoc] using hr
    · right; left
      apply encoded_in_region (x_index_bound cfg ha.1 hk)
      simpa only [Candidate.readByte,hevent,Option.bind_some,Kind.readByte,xLoc] using hr
    · right; right
      apply encoded_in_region (w_index_bound cfg he hk ha.2)
      simpa only [Candidate.readByte,hevent,Option.bind_some,Kind.readByte,wLoc] using hr
    · simp [Candidate.readByte,hevent,Kind.readByte] at hr

theorem write_shape {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.writeByte event loc = some value) :
    event.thread.Valid cfg.geometry ∧ Active cfg event.thread ∧ event.serial = 1+2*cfg.input.k ∧
      ∃ e, e < 2 ∧ ∃ answer : ℝ, payloadByte (hLoc cfg e (row cfg.geometry.block event.thread) (col cfg.geometry.block event.thread))
        (Symbolic.encode .f32 answer) loc = some value := by
  cases hevent : execution.eventAt event with
  | none => simp [Candidate.writeByte,hevent] at hr
  | some kind =>
    obtain ⟨oracle,hv,ha,hcases⟩ := event_shape hw hd hg hp hevent
    rcases hcases with ⟨_,rfl⟩ | ⟨he,⟨_,_,_,rfl⟩ | ⟨_,_,_,rfl⟩ | ⟨hs,rfl⟩⟩
    · simp [Candidate.writeByte,hevent,routeKind,Kind.writeByte] at hr
    · simp [Candidate.writeByte,hevent,Kind.writeByte] at hr
    · simp [Candidate.writeByte,hevent,Kind.writeByte] at hr
    · exact ⟨hv,ha,hs,expert oracle,he,answer cfg oracle,
        by simpa only [Candidate.writeByte,hevent,Option.bind_some,Kind.writeByte] using hr⟩

theorem write_region {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {loc : Location} {value : Symbolic.Byte} (hr : execution.writeByte event loc = some value) :
    InWords cfg.input.h ((2*cfg.input.m)*cfg.input.n) loc := by
  obtain ⟨_,ha,_,e,he,value,hpayload⟩ := write_shape hw hd hg hp hr
  exact encoded_in_region (h_index_bound cfg he ha.1 ha.2) hpayload

theorem access_bounds {cfg : Config} {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = cfg.geometry) (hp : Params cfg.input launch.params)
    {event : EventId} {kind : Scalar.Kind} (he : execution.eventAt event = some kind) :
    ∃ base, kind.footprint = some (base,4) ∧ base.space = .global ∧
      base.address % 4 = 0 ∧ base.address+3 < 2^64 := by
  obtain ⟨oracle,_,ha,hcases⟩ := event_shape hw hd hg hp he
  rcases hcases with ⟨_,rfl⟩ | ⟨hexpert,⟨k,hk,_,rfl⟩ | ⟨k,hk,_,rfl⟩ | ⟨_,rfl⟩⟩
  · exact ⟨_,by simp [routeKind,Kind.footprint,u32_bytes_size],rfl,
      r_aligned cfg ha.1 (by have := ha.2; omega),r_footprint cfg ha.1 (by have := ha.2; omega) (by decide)⟩
  · exact ⟨_,by simp [Kind.footprint,Symbolic.Format.bytes],rfl,
      x_aligned cfg ha.1 hk (by have := ha.2; omega),x_footprint cfg ha.1 hk (by have := ha.2; omega) (by decide)⟩
  · exact ⟨_,by simp [Kind.footprint,Symbolic.Format.bytes],rfl,
      w_aligned cfg hk ha.2 (by have := ha.1; omega),w_footprint cfg hexpert hk ha.2 (by have := ha.1; omega) (by decide)⟩
  · exact ⟨_,by simp [Kind.footprint,Symbolic.Format.bytes],rfl,
      h_aligned cfg ha.1 ha.2,h_footprint cfg hexpert ha.1 ha.2 (by decide)⟩

end
end Ptx.MoeExpertsEvent
