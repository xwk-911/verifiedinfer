import Ptx.Kernels.FloatLiteralsTrace
import Ptx.Scalar.Memory
import Ptx.Event.Equivalence

/-! Shared store/read consistency for the ACTUAL translated float fixture.
These graph-family results quantify over arbitrary real load answers and every
reads-from/coherence witness. All-candidate trace reconstruction and the resulting
contract are in FloatLiteralsUniversal.
No allocation, IEEE arithmetic or CUDA runtime correspondence is inferred.
-/
namespace Ptx.FloatLiteralsMemory
open Ptx.ISA Ptx.Event
noncomputable section

def thread : ThreadId := ⟨.zero,.zero⟩
def sharedLoc : Location := ⟨.shared .zero,0⟩
def globalLoc (dst : Nat) : Location := ⟨.global,dst⟩
def storeId : EventId := ⟨thread,0⟩
def readId : EventId := ⟨thread,1⟩
def outputId : EventId := ⟨thread,2⟩

def trace (dst : Nat) (answer : ℝ) : Scalar.ThreadTrace := {
  id := thread
  oracle := fun _ => .real .f32 answer
  count := 8
  final := (FloatLiteralsTrace.finalState dst answer).core
  events := FloatLiteralsTrace.events thread dst answer
}
def graph (dst : Nat) (answer : ℝ) : Scalar.Candidate := ⟨[trace dst answer]⟩
def launch (dst : Nat) (initial : Scalar.ByteMap) : Scalar.Launch :=
  ⟨⟨.one,.one⟩,[("dst",dst)],initial⟩

theorem produced (dst : Nat) (answer : ℝ) (hd : dst < 2^64) :
    Scalar.Produced FloatLiteralsTrace.code [("dst",dst)] (trace dst answer) :=
  ⟨(FloatLiteralsTrace.finalState dst answer).floats,
    FloatLiteralsTrace.translated_trace {id := thread,params := [("dst",dst)]} dst answer rfl hd⟩

theorem valid_thread_unique {id : ThreadId} (h : id.Valid ⟨.one,.one⟩) : id = thread := by
  rcases id with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
  simp only [ThreadId.Valid,Dim3.Within,Dim3.one] at h
  have hz : cx = 0 ∧ cy = 0 ∧ cz = 0 ∧ tx = 0 ∧ ty = 0 ∧ tz = 0 := by omega
  rcases hz with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  rfl

theorem wellFormed (dst : Nat) (answer : ℝ) (initial : Scalar.ByteMap) (hd : dst < 2^64) :
    Scalar.WellFormed FloatLiteralsTrace.code (launch dst initial) (graph dst answer) := by
  refine ⟨by simp [launch,Geometry.Valid,Dim3.Positive,Dim3.one],
    by simp [graph],?_,?_⟩
  · intro t ht
    simp only [graph,List.mem_singleton] at ht
    subst t
    exact ⟨by simp [trace,thread,ThreadId.Valid,Dim3.Within,launch,Dim3.one,Dim3.zero],produced dst answer hd⟩
  · intro id hv
    have hi := valid_thread_unique hv
    exact ⟨trace dst answer,by simp [graph],hi.symm⟩

theorem complete (dst : Nat) (answer : ℝ) : (graph dst answer).Complete := by
  intro t ht
  simp only [graph,List.mem_singleton] at ht
  subst t
  rfl

theorem eventAt (dst : Nat) (answer : ℝ) (id : EventId) :
    (graph dst answer).eventAt id =
      if id.thread = thread then (FloatLiteralsTrace.events thread dst answer)[id.serial]? else none := by
  by_cases h : id.thread = thread
  · simp [Candidate.eventAt,graph,trace,h]
  · simp [Candidate.eventAt,graph,trace,h,beq_iff_eq,Ne.symm h]

theorem event_shape {dst answer id kind} (he : (graph dst answer).eventAt id = some kind) :
    id.thread = thread ∧
      ((id.serial = 0 ∧ kind = .write sharedLoc (Symbolic.encode .f32 9)) ∨
       (id.serial = 1 ∧ kind = .read sharedLoc (Symbolic.encode .f32 answer)) ∨
       (id.serial = 2 ∧ kind = .write (globalLoc dst) (Symbolic.encode .f32 answer))) := by
  rw [eventAt] at he
  split at he
  · rename_i hi
    refine ⟨hi,?_⟩
    have hb := (List.getElem?_eq_some_iff.mp he).1
    simp only [FloatLiteralsTrace.events,List.length_cons,List.length_nil] at hb
    have hs : id.serial = 0 ∨ id.serial = 1 ∨ id.serial = 2 := by omega
    rcases hs with hs | hs | hs
    · exact .inl ⟨hs,by simpa [FloatLiteralsTrace.events,hs,sharedLoc,thread] using he.symm⟩
    · exact .inr (.inl ⟨hs,by simpa [FloatLiteralsTrace.events,hs,sharedLoc,thread] using he.symm⟩)
    · exact .inr (.inr ⟨hs,by simpa [FloatLiteralsTrace.events,hs,globalLoc] using he.symm⟩)
  · cases he

theorem read_shape {dst answer id loc value}
    (hr : (graph dst answer).readByte id loc = some value) :
    id = readId ∧ payloadByte sharedLoc (Symbolic.encode .f32 answer) loc = some value := by
  cases he : (graph dst answer).eventAt id with
  | none => simp [Candidate.readByte,he] at hr
  | some kind =>
    obtain ⟨hi,hk⟩ := event_shape he
    rcases hk with ⟨hs,rfl⟩ | ⟨hs,rfl⟩ | ⟨hs,rfl⟩
    · simp [Candidate.readByte,he,Kind.readByte] at hr
    · exact ⟨by cases id; simp_all [readId],by simpa [Candidate.readByte,he,Kind.readByte] using hr⟩
    · simp [Candidate.readByte,he,Kind.readByte] at hr

theorem write_shape {dst answer id loc value}
    (hw : (graph dst answer).writeByte id loc = some value) :
    (id = storeId ∧ payloadByte sharedLoc (Symbolic.encode .f32 9) loc = some value) ∨
    (id = outputId ∧ payloadByte (globalLoc dst) (Symbolic.encode .f32 answer) loc = some value) := by
  cases he : (graph dst answer).eventAt id with
  | none => simp [Candidate.writeByte,he] at hw
  | some kind =>
    obtain ⟨hi,hk⟩ := event_shape he
    rcases hk with ⟨hs,rfl⟩ | ⟨hs,rfl⟩ | ⟨hs,rfl⟩
    · exact .inl ⟨by cases id; simp_all [storeId],by simpa [Candidate.writeByte,he,Kind.writeByte] using hw⟩
    · simp [Candidate.writeByte,he,Kind.writeByte] at hw
    · exact .inr ⟨by cases id; simp_all [outputId],by simpa [Candidate.writeByte,he,Kind.writeByte] using hw⟩

theorem no_races (dst : Nat) (answer : ℝ) (rf : ReadsFrom) (a b : EventId) :
    ¬ DataRace (graph dst answer) rf a b := by
  intro hr
  obtain ⟨loc,ha,hb⟩ := hr.overlap
  have shape : ∀ id, (graph dst answer).Accesses id loc →
      id.thread = thread ∧ ((graph dst answer).eventAt id).bind Kind.footprint =
        some (⟨loc.space,if loc.space = .global then dst else 0⟩,4) := by
    intro id h
    have hp := accesses_present h
    cases he : (graph dst answer).eventAt id with
    | none => simp [he] at hp
    | some kind =>
      obtain ⟨hi,hk⟩ := event_shape he
      refine ⟨hi,?_⟩
      rcases hk with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩
      all_goals
        simp only [Candidate.Accesses,Candidate.readByte,Candidate.writeByte,he,
          Option.bind_some,Kind.readByte,Kind.writeByte,Option.isSome_none,Bool.false_eq_true,
          false_or,or_false] at h
        obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp h
        have hs := (payloadByte_bounds hv).1
        simp only [sharedLoc,globalLoc] at hs
        simp [Kind.footprint,hs.symm,sharedLoc,globalLoc,Symbolic.Format.bytes]
  obtain ⟨hia,hfa⟩ := shape a ha
  obtain ⟨hib,hfb⟩ := shape b hb
  exact hr.notStrong ⟨Or.inl (hia.trans hib.symm),_,hfa,hfb⟩

theorem shared_read_correct {dst answer initial rf co}
    (hc : GenericMemoryConditions (graph dst answer) initial rf co) : answer = 9 := by
  have he := race_free_eligible (no_races dst answer rf) readId sharedLoc
  have hw : (graph dst answer).writeByte storeId sharedLoc = some (.realPart .f32 9 0) := by
    simp [Candidate.writeByte,eventAt,storeId,Kind.writeByte,FloatLiteralsTrace.events,
      sharedLoc,payloadByte,Symbolic.encode,Symbolic.Format.bytes,List.range_succ,thread]
  have hr : (graph dst answer).readByte readId sharedLoc = some (.realPart .f32 answer 0) := by
    simp [Candidate.readByte,eventAt,readId,Kind.readByte,FloatLiteralsTrace.events,
      sharedLoc,payloadByte,Symbolic.encode,Symbolic.Format.bytes,List.range_succ,thread]
  have hbefore : Causality (graph dst answer) rf storeId readId := by
    apply causal_of_base
    · exact ⟨sharedLoc,.inr (by rw [hw]; rfl),.inl (by rw [hr]; rfl)⟩
    · apply program_causal
      simp [ProgramOrder,Candidate.Present,eventAt,storeId,readId,FloatLiteralsTrace.events]
  have hu : ∀ other value, (graph dst answer).writeByte other sharedLoc = some value → other = storeId := by
    intro other value h
    rcases write_shape h with ⟨hi,_⟩ | ⟨_,hb⟩
    · exact hi
    · have hs := (payloadByte_bounds hb).1
      cases hs
  have hv := unique_writer_visible hc he hw hr hbefore hu
  exact (Symbolic.Byte.realPart.inj hv).2.1

theorem wrong_answer_rejected (dst : Nat) (initial : Scalar.ByteMap) (rf : ReadsFrom) (co : Coherence) :
    ¬ GenericMemoryConditions (graph dst 17) initial rf co := by
  intro hc
  have h := shared_read_correct hc
  norm_num at h

theorem unique_writer {dst answer loc a b va vb}
    (ha : (graph dst answer).writeByte a loc = some va)
    (hb : (graph dst answer).writeByte b loc = some vb) : a = b := by
  rcases write_shape ha with ⟨hia,hpa⟩ | ⟨hia,hpa⟩ <;>
    rcases write_shape hb with ⟨hib,hpb⟩ | ⟨hib,hpb⟩
  · exact hia.trans hib.symm
  · have hs := (payloadByte_bounds hpa).1.trans (payloadByte_bounds hpb).1.symm
    cases hs
  · have hs := (payloadByte_bounds hpa).1.trans (payloadByte_bounds hpb).1.symm
    cases hs
  · exact hia.trans hib.symm

theorem no_returns (dst : Nat) (answer : ℝ) (id bid generation) :
    (graph dst answer).eventAt id ≠ some (.barrierReturn bid generation) := by
  intro he
  obtain ⟨_,hk⟩ := event_shape he
  rcases hk with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ <;> cases h

/-- Constructive model witness for arbitrary initial memory. The read's source
is the actual shared write; no source values or correctness hypotheses are added. -/
theorem consistent (dst : Nat) (initial : Scalar.ByteMap) :
    GenericMemoryConditions (graph dst 9) initial (fun _ _ => .write storeId) (InitialCo (graph dst 9)) := by
  apply initial_co_conditions (fun id => id.serial)
  · intro a b h
    exact h.2.2.2
  · intro a b h
    obtain ⟨_,bid,generation,_,hb⟩ := h
    exact (no_returns dst 9 b bid generation hb).elim
  · intro a b h
    obtain ⟨_,t,_,_,_,bid,generation,hb,_⟩ := h
    exact (no_returns dst 9 b bid generation hb).elim
  · intro leave bid generation he
    exact (no_returns dst 9 leave bid generation he).elim
  · intro loc a b va vb ha hb
    exact unique_writer ha hb
  · intro read loc value hr
    obtain ⟨_,hv⟩ := read_shape hr
    simpa [sourceByte,Candidate.writeByte,eventAt,storeId,FloatLiteralsTrace.events,
      Kind.writeByte,sharedLoc,thread] using hv
  · intro read writer loc vr vw hr hw hs
    obtain ⟨rfl,_⟩ := read_shape hr
    have hi : writer = storeId := Source.write.inj hs.symm
    subst writer
    decide
  · intro read writer loc vr vw hr hw hs
    cases hs

def domain (dst : Nat) : List Location := (List.range 4).map (globalLoc dst).add
def observedValue (dst : Nat) (output : Scalar.ByteMap) : Option ℝ :=
  Symbolic.decode .f32 ((List.range 4).map (fun offset => output ((globalLoc dst).add offset)))

theorem global_writer {dst answer id loc value}
    (hg : loc.space = .global) (hw : (graph dst answer).writeByte id loc = some value) : id = outputId := by
  rcases write_shape hw with ⟨_,hp⟩ | ⟨hi,_⟩
  · have hs := (payloadByte_bounds hp).1
    simp [sharedLoc,hg] at hs
  · exact hi

theorem output_byte {dst answer initial rf co o offset}
    (hc : GenericMemoryConditions (graph dst answer) initial rf co)
    (ho : ObserverConditions (graph dst answer) initial rf co o)
    (hd : o.domain = domain dst) (hb : offset < 4) :
    o.output ((globalLoc dst).add offset) = .realPart .f32 9 offset := by
  have hans := shared_read_correct hc
  subst answer
  have hw : (graph dst 9).writeByte outputId ((globalLoc dst).add offset) =
      some (.realPart .f32 9 offset) := by
    simp only [Candidate.writeByte,eventAt,outputId,↓reduceIte,FloatLiteralsTrace.events,
      List.getElem?_cons_succ,List.getElem?_cons_zero,Option.bind_some,Kind.writeByte,
      show (⟨AddressSpace.global,dst⟩ : Location) = globalLoc dst by rfl,payloadByte_offset]
    simp [Symbolic.encode,Symbolic.Format.bytes,List.getElem?_map,List.getElem?_range hb]
  apply observer_unique_writer hc ho
  · rw [hd]
    exact List.mem_map.mpr ⟨offset,List.mem_range.mpr hb,rfl⟩
  · exact race_free_observer_eligible (no_races dst 9 rf) _
  · exact hw
  · intro other value h
    exact unique_writer h hw

theorem output_correct {dst answer initial rf co o}
    (hc : GenericMemoryConditions (graph dst answer) initial rf co)
    (ho : ObserverConditions (graph dst answer) initial rf co o)
    (hd : o.domain = domain dst) : observedValue dst o.output = some 9 := by
  have hans := shared_read_correct hc
  subst answer
  change Scalar.readReal .f32 o.output (globalLoc dst) = some 9
  apply Scalar.represents_read
  apply Scalar.observe_real_write (writer := outputId) hc ho
  · simp [eventAt,outputId,FloatLiteralsTrace.events,globalLoc]
  · intro offset hb
    rw [hd]
    exact List.mem_map.mpr ⟨offset,List.mem_range.mpr hb,rfl⟩
  · intro offset _
    exact race_free_observer_eligible (no_races dst 9 rf) _
  · intro offset hb other value hw
    apply unique_writer hw
    simpa only [Candidate.writeByte,eventAt,outputId,↓reduceIte,FloatLiteralsTrace.events,
      List.getElem?_cons_succ,List.getElem?_cons_zero,Option.bind_some,Kind.writeByte,
      show (⟨AddressSpace.global,dst⟩ : Location) = globalLoc dst by rfl] using
      Scalar.encoded_byte .f32 9 (globalLoc dst) hb

def observation (dst : Nat) (initial : Scalar.ByteMap) : Scalar.Observation :=
  selectedObservation (graph dst 9) initial (fun _ => some outputId) (domain dst)

theorem observed (dst : Nat) (initial : Scalar.ByteMap) :
    ObserverConditions (graph dst 9) initial (fun _ _ => .write storeId)
      (InitialCo (graph dst 9)) (observation dst initial) := by
  apply selected_observation_on_domain (complete dst 9)
  · intro loc hm
    obtain ⟨offset,_,rfl⟩ := List.mem_map.mp hm
    rfl
  · intro loc hm writer value hw
    obtain ⟨offset,_,rfl⟩ := List.mem_map.mp hm
    rw [global_writer rfl hw]

theorem observed_execution_exists (dst : Nat) (initial : Scalar.ByteMap) (hd : dst < 2^64) :
    ∃ c rf co o, Scalar.WellFormed FloatLiteralsTrace.code (launch dst initial) c ∧
      GenericMemoryConditions c initial rf co ∧ ObserverConditions c initial rf co o ∧
      o.domain = domain dst ∧ observedValue dst o.output = some 9 := by
  exact ⟨graph dst 9,fun _ _ => .write storeId,InitialCo (graph dst 9),observation dst initial,
    wellFormed dst 9 initial hd,consistent dst initial,observed dst initial,rfl,
    output_correct (consistent dst initial) (observed dst initial) rfl⟩

end
end Ptx.FloatLiteralsMemory
