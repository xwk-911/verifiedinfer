import Ptx.Event.Execution

/-! Bytewise memory footprints and reads-from witnesses for ordinary generic
accesses. These definitions are components of consistency, not a PTX-consistency
predicate on their own. In particular value agreement must only be applied to
reads proved untainted when mixed-size races have been excluded. -/
namespace Ptx.Event
open Ptx.ISA

variable {ByteValue Answers : Type}

def payloadByte (base : Location) (bytes : List ByteValue) (loc : Location) : Option ByteValue :=
  if base.space = loc.space ∧ base.address ≤ loc.address then
    bytes[loc.address - base.address]?
  else none

@[simp] theorem payloadByte_offset (base : Location) (bytes : List ByteValue) (offset : Nat) :
    payloadByte base bytes (base.add offset) = bytes[offset]? := by
  simp [payloadByte, Location.add]

theorem payloadByte_other_space {base loc : Location} (bytes : List ByteValue)
    (h : base.space ≠ loc.space) : payloadByte base bytes loc = none := by
  simp [payloadByte, h]

theorem payloadByte_before {base loc : Location} (bytes : List ByteValue)
    (h : loc.address < base.address) : payloadByte base bytes loc = none := by
  simp [payloadByte, show ¬ base.address ≤ loc.address by omega]

theorem payloadByte_mem {base loc : Location} {bytes : List ByteValue} {value : ByteValue} (h : payloadByte base bytes loc = some value) :
    value ∈ bytes := by
  unfold payloadByte at h
  split at h
  · exact List.mem_of_getElem? h
  · cases h

theorem payloadByte_bounds {base loc : Location} {bytes : List ByteValue} {value : ByteValue} (h : payloadByte base bytes loc = some value) :
    base.space = loc.space ∧ base.address ≤ loc.address ∧ loc.address < base.address + bytes.length := by
  unfold payloadByte at h
  split at h
  · rename_i hg
    have hn := (List.getElem?_eq_some_iff.mp h).1
    exact ⟨hg.1, hg.2, by omega⟩
  · cases h

def Kind.readByte (kind : Kind ByteValue) (loc : Location) : Option ByteValue :=
  match kind with
  | .read base bytes => payloadByte base bytes loc
  | .rmw _ base bytes => payloadByte base bytes.before loc
  | _ => none

def Kind.writeByte (kind : Kind ByteValue) (loc : Location) : Option ByteValue :=
  match kind with
  | .write base bytes => payloadByte base bytes loc
  | .rmw _ base bytes => payloadByte base bytes.after loc
  | _ => none

def Kind.footprint (kind : Kind ByteValue) : Option (Location × Nat) :=
  match kind with
  | .read base bytes | .write base bytes => some (base, bytes.length)
  | .rmw _ base bytes => some (base,bytes.before.length)
  | _ => none

def Candidate.readByte (c : Candidate ByteValue Answers) (id : EventId) (loc : Location) : Option ByteValue :=
  (c.eventAt id).bind (fun kind => kind.readByte loc)

def Candidate.writeByte (c : Candidate ByteValue Answers) (id : EventId) (loc : Location) : Option ByteValue :=
  (c.eventAt id).bind (fun kind => kind.writeByte loc)

def Candidate.Accesses (c : Candidate ByteValue Answers) (id : EventId) (loc : Location) : Prop :=
  (c.readByte id loc).isSome = true ∨ (c.writeByte id loc).isSome = true

def Candidate.Writes (c : Candidate ByteValue Answers) (id : EventId) : Prop :=
  ∃ loc value, c.writeByte id loc = some value

def Candidate.Overlap (c : Candidate ByteValue Answers) (a b : EventId) : Prop :=
  ∃ loc, c.Accesses a loc ∧ c.Accesses b loc

def Candidate.SameFootprint (c : Candidate ByteValue Answers) (a b : EventId) : Prop :=
  ∃ footprint, (c.eventAt a).bind Kind.footprint = some footprint ∧
    (c.eventAt b).bind Kind.footprint = some footprint

theorem accesses_present {c : Candidate ByteValue Answers} {id loc} (h : Candidate.Accesses c id loc) :
    (c.eventAt id).isSome = true := by
  cases he : c.eventAt id with
  | none => simp [Candidate.Accesses, Candidate.readByte, Candidate.writeByte, he] at h
  | some kind => rfl

theorem access_footprint_bounds {c : Candidate ByteValue Answers} {id loc base size}
    (ha : c.Accesses id loc) (hf : (c.eventAt id).bind Kind.footprint = some (base,size)) :
    base.space = loc.space ∧ base.address ≤ loc.address ∧ loc.address < base.address+size := by
  cases he : c.eventAt id with
  | none => simp [Candidate.Accesses,Candidate.readByte,Candidate.writeByte,he] at ha
  | some kind =>
    cases kind with
    | read start bytes =>
      simp only [he,Option.bind_some,Kind.footprint,Option.some.injEq,Prod.mk.injEq] at hf
      rcases hf with ⟨rfl,rfl⟩
      rcases ha with hr | hw
      · obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp hr
        exact payloadByte_bounds (by simpa [Candidate.readByte,he,Kind.readByte] using hv)
      · simp [Candidate.writeByte,he,Kind.writeByte] at hw
    | write start bytes =>
      simp only [he,Option.bind_some,Kind.footprint,Option.some.injEq,Prod.mk.injEq] at hf
      rcases hf with ⟨rfl,rfl⟩
      rcases ha with hr | hw
      · simp [Candidate.readByte,he,Kind.readByte] at hr
      · obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp hw
        exact payloadByte_bounds (by simpa [Candidate.writeByte,he,Kind.writeByte] using hv)
    | rmw scope start bytes =>
      simp only [he,Option.bind_some,Kind.footprint,Option.some.injEq,Prod.mk.injEq] at hf
      rcases hf with ⟨rfl,rfl⟩
      rcases ha with hr | hw
      · obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp hr
        exact payloadByte_bounds (by simpa [Candidate.readByte,he,Kind.readByte] using hv)
      · obtain ⟨value,hv⟩ := Option.isSome_iff_exists.mp hw
        have hb := payloadByte_bounds (by simpa [Candidate.writeByte,he,Kind.writeByte] using hv)
        simpa only [bytes.sameSize] using hb
    | barrierArrival bid generation => simp [he,Kind.footprint] at hf
    | barrierReturn bid generation => simp [he,Kind.footprint] at hf

def Candidate.IsRMW (c : Candidate ByteValue Answers) (id : EventId) : Prop :=
  ∃ scope base bytes, c.eventAt id = some (.rmw scope base bytes)

/-- Ordinary reads/writes are exclusive; a true RMW has both projections. -/
theorem read_write_requires_rmw {c : Candidate ByteValue Answers} {id readLoc writeLoc readValue writeValue}
    (hr : Candidate.readByte c id readLoc = some readValue)
    (hw : Candidate.writeByte c id writeLoc = some writeValue) : c.IsRMW id := by
  cases he : c.eventAt id with
  | none => simp [Candidate.readByte,he] at hr
  | some kind =>
    cases kind with
    | rmw scope base bytes => exact ⟨scope,base,bytes,he⟩
    | _ => simp [Candidate.readByte,Candidate.writeByte,he,Kind.readByte,Kind.writeByte] at hr hw

theorem read_write_exclusive {c : Candidate ByteValue Answers} {id readLoc writeLoc readValue writeValue}
    (hn : ¬ c.IsRMW id) (hr : c.readByte id readLoc = some readValue)
    (hw : c.writeByte id writeLoc = some writeValue) : False :=
  hn (read_write_requires_rmw hr hw)

inductive Source
  | initial
  | write (id : EventId)
  deriving Repr, DecidableEq

/-- A separate source for each read byte; a u32 read need not have one source. -/
abbrev ReadsFrom := EventId → Location → Source

def sourceByte (c : Candidate ByteValue Answers) (initial : ByteMap ByteValue) (loc : Location) : Source → Option ByteValue
  | .initial => some (initial loc)
  | .write id => c.writeByte id loc

/-- Eligibility must be discharged by the consistency/race analysis. Taking it
to be True indiscriminately would incorrectly constrain racing PTX loads. -/
def ValueAgreement (c : Candidate ByteValue Answers) (initial : ByteMap ByteValue)
    (eligible : EventId → Location → Prop) (rf : ReadsFrom) : Prop :=
  ∀ read loc value, eligible read loc → c.readByte read loc = some value →
    sourceByte c initial loc (rf read loc) = some value

theorem initial_read_value {c : Candidate ByteValue Answers} {initial eligible rf read loc value}
    (ha : ValueAgreement c initial eligible rf) (he : eligible read loc)
    (hr : c.readByte read loc = some value) (hs : rf read loc = .initial) :
    value = initial loc := by
  have h := ha read loc value he hr
  rw [hs] at h
  exact (Option.some.inj h).symm

theorem write_read_value {c : Candidate ByteValue Answers} {initial eligible rf read loc value writer}
    (ha : ValueAgreement c initial eligible rf) (he : eligible read loc)
    (hr : c.readByte read loc = some value) (hs : rf read loc = .write writer) :
    c.writeByte writer loc = some value := by
  have h := ha read loc value he hr
  simpa [hs, sourceByte] using h

/-- No kernel writes this byte, so an eligible read must see its fixed initial
byte. This does not infer that a read is eligible or that the graph is consistent. -/
theorem unwritten_read_initial {c : Candidate ByteValue Answers} {initial eligible rf read loc value}
    (ha : ValueAgreement c initial eligible rf) (he : eligible read loc)
    (hr : c.readByte read loc = some value)
    (hn : ∀ writer, c.writeByte writer loc = none) : value = initial loc := by
  cases hs : rf read loc with
  | initial => exact initial_read_value ha he hr hs
  | write writer =>
    have h := write_read_value ha he hr hs
    rw [hn writer] at h
    cases h

end Ptx.Event
