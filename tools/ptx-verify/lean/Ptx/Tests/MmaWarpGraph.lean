import Ptx.Tests.MmaWarp

/-! The actual generated full-warp probe's byte-access inventory. This is
derived from source traces, not supplied as a separate memory graph. -/
namespace Ptx.MmaWarpTests
open Ptx.ISA Ptx.Ampere
noncomputable section

def memoryEvent : Event → Option Scalar.Kind
  | .ordinary k => some k
  | _ => none

def inputPair : PackedF16 := ⟨1,1⟩
def outputBytes : List Symbolic.Byte := Symbolic.encode .f32 16
def kinds (lane : Mma.Lane) : List (Option Scalar.Kind) := [
  some (.read ⟨.global,16*lane.val⟩ inputPair.encode),
  some (.read ⟨.global,16*lane.val+4⟩ inputPair.encode),
  some (.read ⟨.global,16*lane.val+8⟩ inputPair.encode),
  some (.read ⟨.global,16*lane.val+12⟩ inputPair.encode),
  some (.read ⟨.global,512+8*lane.val⟩ inputPair.encode),
  some (.read ⟨.global,512+8*lane.val+4⟩ inputPair.encode),
  none,none,
  some (.write ⟨.global,768+16*lane.val⟩ outputBytes),
  some (.write ⟨.global,768+16*lane.val+4⟩ outputBytes),
  some (.write ⟨.global,768+16*lane.val+8⟩ outputBytes),
  some (.write ⟨.global,768+16*lane.val+12⟩ outputBytes)]

theorem emitted_memory_kinds (lane : Mma.Lane) : (trace lane).events.map memoryEvent = kinds lane := by
  fin_cases lane <;> rfl

theorem memory_kind (lane : Mma.Lane) (serial : Nat) :
    candidate.memoryKind (.thread ⟨id lane,serial⟩) = (kinds lane)[serial]?.join := by
  change ((candidate.traceAt (id lane)).bind (fun t => t.events[serial]?)).bind memoryEvent = _
  rw [trace_at]
  change ((trace lane).events[serial]?).bind memoryEvent = _
  rw [← emitted_memory_kinds,List.getElem?_map]
  cases (trace lane).events[serial]? <;> rfl

theorem trace_no_copies (lane : Mma.Lane) : (trace lane).final.copies = [] := by
  fin_cases lane <;> rfl

theorem no_copies (operation : CopyId) : candidate.copyAt operation = none := by
  cases hc : candidate.copyAt operation with
  | none => rfl
  | some op =>
    obtain ⟨t,ht,_,hi⟩ := copyAt_trace hc
    obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
    rw [trace_no_copies] at hi
    cases hi

theorem memory_owner {event kind} (he : candidate.eventAt event = some kind) :
    ∃ lane, event.thread = id lane := by
  obtain ⟨t,ht,hid,_⟩ := eventAt_trace he
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  exact ⟨lane,hid.symm⟩

def readBase (lane : Mma.Lane) (i : Fin 6) : Location :=
  ⟨.global,if i.val < 4 then 16*lane.val+4*i.val else 512+8*lane.val+4*(i.val-4)⟩
def writeBase (lane : Mma.Lane) (i : Fin 4) : Location := ⟨.global,768+16*lane.val+4*i.val⟩
def readNode (lane : Mma.Lane) (i : Fin 6) : Node := .thread ⟨id lane,i.val⟩
def writeNode (lane : Mma.Lane) (i : Fin 4) : Node := .thread ⟨id lane,8+i.val⟩

theorem read_kind (lane : Mma.Lane) (i : Fin 6) :
    candidate.memoryKind (readNode lane i) = some (.read (readBase lane i) inputPair.encode) := by
  unfold readNode
  rw [memory_kind]
  fin_cases i <;> rfl

theorem write_kind (lane : Mma.Lane) (i : Fin 4) :
    candidate.memoryKind (writeNode lane i) = some (.write (writeBase lane i) outputBytes) := by
  unfold writeNode
  rw [memory_kind]
  fin_cases i <;> rfl

theorem memory_node_owner {node kind} (hk : candidate.memoryKind node = some kind) :
    ∃ lane serial, node = .thread ⟨id lane,serial⟩ := by
  cases node with
  | copyRead op | copyWrite op => simp [Candidate.memoryKind,no_copies] at hk
  | thread event =>
    cases he : candidate.eventAt event with
    | none => simp [Candidate.memoryKind,he] at hk
    | some e =>
      obtain ⟨lane,hid⟩ := memory_owner he
      exact ⟨lane,event.serial,by cases event; simp_all⟩

theorem read_cases {node loc value} (hr : candidate.readByte node loc = some value) :
    ∃ lane i, node = readNode lane i ∧ Ptx.Event.payloadByte (readBase lane i) inputPair.encode loc = some value := by
  cases hk : candidate.memoryKind node with
  | none => simp [Candidate.readByte,hk] at hr
  | some kind =>
    obtain ⟨lane,serial,rfl⟩ := memory_node_owner hk
    rw [Candidate.readByte,memory_kind] at hr
    have hs : serial < 12 := by
      by_contra hn
      have hh : (kinds lane)[serial]? = none := List.getElem?_eq_none (by change 12 ≤ serial; omega)
      simp [hh] at hr
    interval_cases serial <;> simp [kinds,Ptx.Event.Kind.readByte] at hr
    · exact ⟨lane,0,rfl,hr⟩
    · exact ⟨lane,1,rfl,hr⟩
    · exact ⟨lane,2,rfl,hr⟩
    · exact ⟨lane,3,rfl,hr⟩
    · exact ⟨lane,4,rfl,hr⟩
    · exact ⟨lane,5,rfl,hr⟩

theorem write_cases {node loc value} (hw : candidate.writeByte node loc = some value) :
    ∃ lane i, node = writeNode lane i ∧ Ptx.Event.payloadByte (writeBase lane i) outputBytes loc = some value := by
  cases hk : candidate.memoryKind node with
  | none => simp [Candidate.writeByte,hk] at hw
  | some kind =>
    obtain ⟨lane,serial,rfl⟩ := memory_node_owner hk
    rw [Candidate.writeByte,memory_kind] at hw
    have hs : serial < 12 := by
      by_contra hn
      have hh : (kinds lane)[serial]? = none := List.getElem?_eq_none (by change 12 ≤ serial; omega)
      simp [hh] at hw
    interval_cases serial <;> simp [kinds,Ptx.Event.Kind.writeByte] at hw
    · exact ⟨lane,0,rfl,hw⟩
    · exact ⟨lane,1,rfl,hw⟩
    · exact ⟨lane,2,rfl,hw⟩
    · exact ⟨lane,3,rfl,hw⟩

end
end Ptx.MmaWarpTests
