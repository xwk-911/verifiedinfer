import Ptx.Scalar.Execution

/-! Reusable symbolic-real input and observation rules. Premises describe the
actual emitted accesses, initialization, eligibility and writer uniqueness.
They do not assume the load answer or kernel result being proved. -/
namespace Ptx.Scalar
open Ptx.ISA Ptx.Event
noncomputable section

def RepresentsReal (format : Symbolic.Format) (memory : ByteMap) (base : Location) (value : ℝ) : Prop :=
  ∀ offset, offset < format.bytes → memory (base.add offset) = .realPart format value offset

def readReal (format : Symbolic.Format) (memory : ByteMap) (base : Location) : Option ℝ :=
  Symbolic.decode format ((List.range format.bytes).map (fun offset => memory (base.add offset)))

theorem represents_read {format memory base value} (h : RepresentsReal format memory base value) :
    readReal format memory base = some value := by
  have he : (List.range format.bytes).map (fun offset => memory (base.add offset)) = Symbolic.encode format value := by
    apply List.map_congr_left
    intro offset hm
    exact h offset (List.mem_range.mp hm)
  simp only [readReal,he,Symbolic.decode_encode]

theorem read_represents {format memory base value} (h : readReal format memory base = some value) :
    RepresentsReal format memory base value := by
  have he := Symbolic.decode_eq_some_iff.mp h
  intro offset ho
  have hh := congrArg (fun bytes => bytes[offset]?) he
  simpa [Symbolic.encode,List.getElem?_map,List.getElem?_range ho] using hh

theorem encoded_byte (format : Symbolic.Format) (value : ℝ) (base : Location) {offset : Nat}
    (hb : offset < format.bytes) :
    payloadByte base (Symbolic.encode format value) (base.add offset) = some (.realPart format value offset) := by
  rw [payloadByte_offset]
  simp [Symbolic.encode,List.getElem?_map,List.getElem?_range hb]

theorem represented_payload {format initial base expected loc value}
    (hi : RepresentsReal format initial base expected)
    (hb : payloadByte base (Symbolic.encode format expected) loc = some value) : initial loc = value := by
  have hbounds := payloadByte_bounds hb
  rw [Symbolic.encode_length] at hbounds
  let offset := loc.address-base.address
  have ho : offset < format.bytes := by dsimp [offset]; omega
  have hl : loc = base.add offset := by
    rcases loc with ⟨space,address⟩
    rcases base with ⟨baseSpace,baseAddress⟩
    simp only at hbounds
    simp only [Location.add,Location.mk.injEq]
    exact ⟨hbounds.1.symm,by dsimp [offset]; omega⟩
  rw [hl,encoded_byte format expected base ho] at hb
  exact (hl ▸ hi offset ho).trans (Option.some.inj hb)

/-- A scalar read emits a complete real encoding. The first fragment identifies
its real value; eligibility and absence of writes are independent client duties. -/
theorem immutable_real_load {c : Candidate} {initial rf format read base answer expected}
    (hm : ValueAgreement c initial (Eligible c rf) rf)
    (hr : c.eventAt read = some (.read base (Symbolic.encode format answer)))
    (he : Eligible c rf read base) (hn : ∀ writer, c.writeByte writer base = none)
    (hi : RepresentsReal format initial base expected) : answer = expected := by
  have hb : 0 < format.bytes := by cases format <;> decide
  have hfirst := encoded_byte format answer base hb
  simp only [Location.add,Nat.add_zero] at hfirst
  have hread : c.readByte read base = some (.realPart format answer 0) := by
    simpa only [Candidate.readByte,hr,Option.bind_some,Kind.readByte] using hfirst
  have hv := unwritten_read_initial hm he hread hn
  have hinit := hi 0 hb
  simp only [Location.add,Nat.add_zero] at hinit
  rw [hinit] at hv
  exact (Symbolic.Byte.realPart.inj hv).2.1

theorem observe_real_write {c : Candidate} {initial rf co o format writer base value}
    (hm : GenericMemoryConditions c initial rf co)
    (ho : ObserverConditions c initial rf co o)
    (hw : c.eventAt writer = some (.write base (Symbolic.encode format value)))
    (hd : ∀ offset, offset < format.bytes → base.add offset ∈ o.domain)
    (he : ∀ offset, offset < format.bytes → ObserverEligible c rf (base.add offset))
    (hu : ∀ offset, offset < format.bytes → ∀ other v,
      c.writeByte other (base.add offset) = some v → other = writer) :
    RepresentsReal format o.output base value := by
  intro offset hb
  apply observer_unique_writer (writer := writer) hm ho (hd offset hb) (he offset hb)
  · simpa only [Candidate.writeByte,hw,Option.bind_some,Kind.writeByte] using encoded_byte format value base hb
  · exact hu offset hb

end
end Ptx.Scalar
