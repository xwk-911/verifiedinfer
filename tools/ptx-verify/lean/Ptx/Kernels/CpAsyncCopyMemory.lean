import Ptx.Kernels.CpAsyncCopyGraph
import Mathlib.Tactic.IntervalCases

/-! Byte footprints and immutable copy input for the actual augmented graph.
The input and output ranges must be disjoint; bytes/answers remain independent.
-/
namespace Ptx.CpAsyncCopyGraph
open Ptx.ISA Ptx.Ampere Ptx.CpAsyncCopyTrace
noncomputable section

def copyId : CopyId := ⟨thread,0⟩
def tile : Location := ⟨.shared .zero,0⟩
def outputNode (i : Fin 4) : Node := .thread ⟨thread,6+2*i.val⟩
def readNode (i : Fin 4) : Node := .thread ⟨thread,5+2*i.val⟩

theorem copy_read_kind (src dst bytes answers) :
    (graph src dst bytes answers).memoryKind (.copyRead copyId) = some (.read ⟨.global,src⟩ bytes) := by
  simp [Candidate.memoryKind,copyAt,copyId,operation]
theorem copy_write_kind (src dst bytes answers) :
    (graph src dst bytes answers).memoryKind (.copyWrite copyId) = some (.write tile bytes) := by
  simp [Candidate.memoryKind,copyAt,copyId,operation,tile,thread]
theorem read_kind (src dst bytes answers) (i : Fin 4) :
    (graph src dst bytes answers).memoryKind (readNode i) =
      some (.read ⟨.shared .zero,4*i.val⟩ (Scalar.u32Bytes (word answers i))) := by
  fin_cases i <;> rfl
theorem output_kind (src dst bytes answers) (i : Fin 4) :
    (graph src dst bytes answers).memoryKind (outputNode i) =
      some (.write ⟨.global,dst+4*i.val⟩ (Scalar.u32Bytes (word answers i))) := by
  fin_cases i <;> rfl

theorem kind_access_bounds {src dst bytes answers node loc kind base size}
    (hk : (graph src dst bytes answers).memoryKind node = some kind)
    (hf : kind.footprint = some (base,size))
    (ha : (graph src dst bytes answers).memoryGraph.Accesses node loc) :
    base.space = loc.space ∧ base.address ≤ loc.address ∧ loc.address < base.address+size :=
  MemoryGraph.access_footprint_bounds ha (by change ((graph src dst bytes answers).memoryKind node).bind _ = _; rw [hk]; exact hf)

theorem copy_before_read {src dst bytes answers} (i : Fin 4) :
    BaseOrder (graph src dst bytes answers) (.copyWrite copyId) (readNode i) := by
  apply Ptx.Event.Path.trans (completed_before_wait (event := ⟨thread,2⟩) ?_)
    (thread_program_causal (b := ⟨thread,5+2*i.val⟩) ?_)
  · exact ⟨rfl,operation thread src bytes,1,0,by simp [copyAt,copyId],rfl,by change (0 : Nat) < 1; decide⟩
  · refine ⟨rfl,?_,rfl,?_⟩
    · fin_cases i <;> rfl
    · change 2 < 5+2*i.val
      omega

theorem output_before_output {src dst bytes answers} {i j : Fin 4} (h : i.val < j.val) :
    BaseOrder (graph src dst bytes answers) (outputNode i) (outputNode j) := by
  apply thread_program_causal (a := ⟨thread,6+2*i.val⟩) (b := ⟨thread,6+2*j.val⟩)
  refine ⟨?_,?_,rfl,?_⟩
  · fin_cases i <;> rfl
  · fin_cases j <;> rfl
  · change 6+2*i.val < 6+2*j.val
    omega

theorem read_cases {src dst bytes answers node loc value}
    (hr : (graph src dst bytes answers).readByte node loc = some value) :
    (node = .copyRead copyId ∧ Ptx.Event.payloadByte ⟨.global,src⟩ bytes loc = some value) ∨
      ∃ i : Fin 4, node = readNode i ∧
        Ptx.Event.payloadByte ⟨.shared .zero,4*i.val⟩ (Scalar.u32Bytes (word answers i)) loc = some value := by
  cases node with
  | copyWrite id =>
    cases hc : (graph src dst bytes answers).copyAt id <;>
      simp [Candidate.readByte,Candidate.memoryKind,hc,Ptx.Event.Kind.readByte] at hr
  | copyRead id =>
    simp only [Candidate.readByte,Candidate.memoryKind,copyAt] at hr
    split at hr
    · rename_i hi
      rcases id with ⟨owner,ordinal⟩
      rcases hi with ⟨rfl,rfl⟩
      exact .inl ⟨rfl,by simpa [operation,Ptx.Event.Kind.readByte] using hr⟩
    · simp at hr
  | thread ev =>
    cases he : (graph src dst bytes answers).eventAt ev with
    | none => simp [Candidate.readByte,Candidate.memoryKind,he] at hr
    | some kind =>
      cases kind with
      | ordinary kind =>
        have hv : kind.readByte loc = some value := by simpa [Candidate.readByte,Candidate.memoryKind,he] using hr
        rw [eventAt] at he
        split at he
        · rename_i howner
          have hb := (List.getElem?_eq_some_iff.mp he).1
          change ev.serial < 13 at hb
          interval_cases hserial : ev.serial <;> cases he
          all_goals simp only [Ptx.Event.Kind.readByte] at hv
          all_goals try cases hv
          · exact .inr ⟨0,by cases ev; simp_all [readNode],hv⟩
          · exact .inr ⟨1,by cases ev; simp_all [readNode],hv⟩
          · exact .inr ⟨2,by cases ev; simp_all [readNode],hv⟩
          · exact .inr ⟨3,by cases ev; simp_all [readNode],hv⟩
        · cases he
      | _ => simp [Candidate.readByte,Candidate.memoryKind,he] at hr

theorem write_cases {src dst bytes answers node loc value}
    (hw : (graph src dst bytes answers).writeByte node loc = some value) :
    (node = .copyWrite copyId ∧ Ptx.Event.payloadByte tile bytes loc = some value) ∨
      ∃ i : Fin 4, node = outputNode i ∧
        Ptx.Event.payloadByte ⟨.global,dst+4*i.val⟩ (Scalar.u32Bytes (word answers i)) loc = some value := by
  cases node with
  | copyRead id =>
    cases hc : (graph src dst bytes answers).copyAt id <;>
      simp [Candidate.writeByte,Candidate.memoryKind,hc,Ptx.Event.Kind.writeByte] at hw
  | copyWrite id =>
    simp only [Candidate.writeByte,Candidate.memoryKind,copyAt] at hw
    split at hw
    · rename_i hi
      rcases id with ⟨owner,ordinal⟩
      rcases hi with ⟨rfl,rfl⟩
      exact .inl ⟨rfl,by simpa [operation,tile,thread,Ptx.Event.Kind.writeByte] using hw⟩
    · simp at hw
  | thread ev =>
    cases he : (graph src dst bytes answers).eventAt ev with
    | none => simp [Candidate.writeByte,Candidate.memoryKind,he] at hw
    | some kind =>
      cases kind with
      | ordinary kind =>
        have hv : kind.writeByte loc = some value := by simpa [Candidate.writeByte,Candidate.memoryKind,he] using hw
        rw [eventAt] at he
        split at he
        · rename_i howner
          have hb := (List.getElem?_eq_some_iff.mp he).1
          change ev.serial < 13 at hb
          interval_cases hserial : ev.serial <;> cases he
          all_goals simp only [Ptx.Event.Kind.writeByte] at hv
          all_goals try cases hv
          · exact .inr ⟨0,by cases ev; simp_all [outputNode],hv⟩
          · exact .inr ⟨1,by cases ev; simp_all [outputNode],hv⟩
          · exact .inr ⟨2,by cases ev; simp_all [outputNode],hv⟩
          · exact .inr ⟨3,by cases ev; simp_all [outputNode],hv⟩
        · cases he
      | _ => simp [Candidate.writeByte,Candidate.memoryKind,he] at hw

theorem input_unwritten {src dst bytes answers} (hdisjoint : src+16 ≤ dst ∨ dst+16 ≤ src)
    (offset : Nat) (ho : offset < 16) (writer : Node) :
    (graph src dst bytes answers).writeByte writer ⟨.global,src+offset⟩ = none := by
  cases hw : (graph src dst bytes answers).writeByte writer ⟨.global,src+offset⟩ with
  | none => rfl
  | some value =>
    rcases write_cases hw with ⟨_,hp⟩ | ⟨i,_,hp⟩
    · have hb := Ptx.Event.payloadByte_bounds hp
      cases hb.1
    · have hb := Ptx.Event.payloadByte_bounds hp
      simp only [Scalar.u32_bytes_size] at hb
      have := i.isLt
      omega

theorem no_race_of_write {src dst bytes answers node other loc value} {rf : ReadsFrom}
    (hsize : bytes.length = 16) (hdisjoint : src+16 ≤ dst ∨ dst+16 ≤ src)
    (hw : (graph src dst bytes answers).writeByte node loc = some value) :
    ¬ MemoryGraph.DataRace (graph src dst bytes answers).memoryGraph rf node other := by
  intro hrace
  obtain ⟨overlapLoc,ha,hb⟩ := hrace.overlap
  rcases write_cases hw with ⟨rfl,_⟩ | ⟨i,rfl,_⟩
  · have haBounds := kind_access_bounds (copy_write_kind src dst bytes answers) rfl ha
    rcases hb with hread | hwrite
    · obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp hread
      rw [graph_readByte] at hv
      rcases read_cases hv with ⟨rfl,hp⟩ | ⟨j,rfl,_⟩
      · have hbBounds := Ptx.Event.payloadByte_bounds hp
        have hs := haBounds.1.trans hbBounds.1.symm
        cases hs
      · exact hrace.notForward (MemoryGraph.causal_of_base hrace.overlap (copy_before_read j))
    · obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp hwrite
      rw [graph_writeByte] at hv
      rcases write_cases hv with ⟨rfl,_⟩ | ⟨j,rfl,hp⟩
      · exact hrace.notStrong (MemoryGraph.write_self_strong (c := (graph src dst bytes answers).memoryGraph) hw)
      · have hbBounds := Ptx.Event.payloadByte_bounds hp
        have hs := haBounds.1.trans hbBounds.1.symm
        cases hs
  · have haBounds := kind_access_bounds (base := ⟨.global,dst+4*i.val⟩) (size := 4) (output_kind src dst bytes answers i)
      (by simp [Ptx.Event.Kind.footprint,Scalar.u32_bytes_size]) ha
    rcases hb with hread | hwrite
    · obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp hread
      rw [graph_readByte] at hv
      rcases read_cases hv with ⟨rfl,hp⟩ | ⟨j,rfl,hp⟩
      · have hbBounds := Ptx.Event.payloadByte_bounds hp
        dsimp only at haBounds hbBounds
        rw [hsize] at hbBounds
        have := i.isLt
        omega
      · have hbBounds := Ptx.Event.payloadByte_bounds hp
        have hs := haBounds.1.trans hbBounds.1.symm
        cases hs
    · obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp hwrite
      rw [graph_writeByte] at hv
      rcases write_cases hv with ⟨rfl,hp⟩ | ⟨j,rfl,_⟩
      · have hbBounds := Ptx.Event.payloadByte_bounds hp
        have hs := haBounds.1.trans hbBounds.1.symm
        cases hs
      · rcases lt_trichotomy i.val j.val with hij | hij | hji
        · exact hrace.notForward (MemoryGraph.causal_of_base hrace.overlap (output_before_output hij))
        · have he : i = j := Fin.ext hij
          subst j
          exact hrace.notStrong (MemoryGraph.write_self_strong (c := (graph src dst bytes answers).memoryGraph) hw)
        · exact hrace.notBackward (MemoryGraph.causal_of_base ⟨overlapLoc,.inr hwrite,ha⟩ (output_before_output hji))

theorem race_free {src dst bytes answers} (hsize : bytes.length = 16)
    (hdisjoint : src+16 ≤ dst ∨ dst+16 ≤ src) (rf : ReadsFrom) (a b : Node) :
    ¬ MemoryGraph.DataRace (graph src dst bytes answers).memoryGraph rf a b := by
  intro hr
  rcases hr.conflict with ⟨loc,value,hw⟩ | ⟨loc,value,hw⟩
  · exact no_race_of_write hsize hdisjoint hw hr
  · exact no_race_of_write hsize hdisjoint hw (MemoryGraph.data_race_symm hr)

/-- Memory agreement, rather than source execution, forces the independent
copy payload to the fixed input map. Eligibility remains an explicit obligation
here; the eventual kernel contract must derive it from source/layout facts. -/
theorem copy_input_bytes {src dst bytes answers initial rf co}
    (hm : MemoryConstraints (graph src dst bytes answers) initial rf co)
    (hb : bytes.length = 16) (hdisjoint : src+16 ≤ dst ∨ dst+16 ≤ src)
    (he : ∀ offset, offset < 16 → MemoryGraph.Eligible (graph src dst bytes answers).memoryGraph rf
      (.copyRead copyId) ⟨.global,src+offset⟩) (offset : Nat) (ho : offset < 16) :
    bytes[offset]? = some (initial ⟨.global,src+offset⟩) := by
  have hindex : offset < bytes.length := by omega
  have hr : (graph src dst bytes answers).memoryGraph.readByte (.copyRead copyId) ⟨.global,src+offset⟩ =
      some bytes[offset] := by
    rw [graph_readByte]
    simp only [Candidate.readByte,Candidate.memoryKind,copyAt,copyId,and_self,ite_eq_left,
      Option.map_some,Option.bind_some,Ptx.Event.Kind.readByte,operation]
    change Ptx.Event.payloadByte (⟨.global,src⟩ : Location) bytes ((⟨.global,src⟩ : Location).add offset) = _
    rw [Ptx.Event.payloadByte_offset,List.getElem?_eq_getElem hindex]
  have hv := MemoryGraph.unwritten_read_initial hm.agreement (he offset ho) hr
    (fun writer => input_unwritten hdisjoint offset ho writer)
  rw [List.getElem?_eq_getElem hindex,hv]

theorem tile_unique_writer {src dst bytes answers loc writer value}
    (hs : loc.space = .shared .zero)
    (hw : (graph src dst bytes answers).writeByte writer loc = some value) : writer = .copyWrite copyId := by
  rcases write_cases hw with ⟨he,_⟩ | ⟨i,_,hp⟩
  · exact he
  · have hb := Ptx.Event.payloadByte_bounds hp
    rw [hs] at hb
    cases hb.1

theorem output_unique_writer {src dst bytes answers writer value} (i : Fin 4) (offset : Nat) (ho : offset < 4)
    (hw : (graph src dst bytes answers).writeByte writer ⟨.global,dst+4*i.val+offset⟩ = some value) :
    writer = outputNode i := by
  rcases write_cases hw with ⟨_,hp⟩ | ⟨j,hnode,hp⟩
  · have hb := Ptx.Event.payloadByte_bounds hp
    cases hb.1
  · have hb := Ptx.Event.payloadByte_bounds hp
    simp only [Scalar.u32_bytes_size] at hb
    have hij : j.val = i.val := by omega
    exact hnode.trans (congrArg outputNode (Fin.ext hij))

theorem load_byte_from_input {src dst bytes answers initial rf co}
    (hm : MemoryConstraints (graph src dst bytes answers) initial rf co)
    (hsize : bytes.length = 16) (hdisjoint : src+16 ≤ dst ∨ dst+16 ≤ src)
    (i : Fin 4) (offset : Nat) (ho : offset < 4) :
    Scalar.u32Byte (word answers i) offset = initial ⟨.global,src+(4*i.val+offset)⟩ := by
  have hidx : 4*i.val+offset < 16 := by have := i.isLt; omega
  have hindex : 4*i.val+offset < bytes.length := by omega
  have hfree := race_free (answers := answers) hsize hdisjoint rf
  have hr : (graph src dst bytes answers).memoryGraph.readByte (readNode i)
      ⟨.shared .zero,4*i.val+offset⟩ = some (Scalar.u32Byte (word answers i) offset) := by
    change ((graph src dst bytes answers).memoryKind (readNode i)).bind _ = _
    rw [read_kind]
    exact Scalar.u32_payload_byte ⟨.shared .zero,4*i.val⟩ (word answers i) offset ho
  have hw : (graph src dst bytes answers).memoryGraph.writeByte (.copyWrite copyId)
      ⟨.shared .zero,4*i.val+offset⟩ = some bytes[4*i.val+offset] := by
    change ((graph src dst bytes answers).memoryKind (.copyWrite copyId)).bind _ = _
    rw [copy_write_kind]
    simpa [tile,Location.add,Ptx.Event.Kind.writeByte] using
      (Ptx.Event.payloadByte_offset tile bytes (4*i.val+offset)).trans (List.getElem?_eq_getElem hindex)
  have hcopied := MemoryGraph.unique_writer_visible (writer := .copyWrite copyId) hm
    (MemoryGraph.race_free_eligible hfree _ _) hw hr
    (MemoryGraph.causal_of_base ⟨⟨.shared .zero,4*i.val+offset⟩,.inr (by rw [hw]; rfl),.inl (by rw [hr]; rfl)⟩ (copy_before_read i))
    (fun other v hv => tile_unique_writer rfl hv)
  have hinitial := copy_input_bytes hm hsize hdisjoint (fun n hn => MemoryGraph.race_free_eligible hfree _ _) (4*i.val+offset) hidx
  rw [List.getElem?_eq_getElem hindex] at hinitial
  exact hcopied.trans (Option.some.inj hinitial)

theorem observed_output_byte {src dst bytes answers initial rf co o}
    (hm : MemoryConstraints (graph src dst bytes answers) initial rf co)
    (hob : ObserverConstraints (graph src dst bytes answers) initial rf co o)
    (hsize : bytes.length = 16) (hdisjoint : src+16 ≤ dst ∨ dst+16 ≤ src)
    (i : Fin 4) (offset : Nat) (ho : offset < 4)
    (hd : (⟨.global,dst+4*i.val+offset⟩ : Location) ∈ o.domain) :
    o.output ⟨.global,dst+4*i.val+offset⟩ = initial ⟨.global,src+(4*i.val+offset)⟩ := by
  have hfree := race_free (answers := answers) hsize hdisjoint rf
  have hw : (graph src dst bytes answers).memoryGraph.writeByte (outputNode i)
      ⟨.global,dst+4*i.val+offset⟩ = some (Scalar.u32Byte (word answers i) offset) := by
    change ((graph src dst bytes answers).memoryKind (outputNode i)).bind _ = _
    rw [output_kind]
    exact Scalar.u32_payload_byte ⟨.global,dst+4*i.val⟩ (word answers i) offset ho
  have hv := MemoryGraph.observer_unique_writer (writer := outputNode i) hm hob hd
    (MemoryGraph.race_free_observer_eligible hfree _) hw
    (fun other v hv => output_unique_writer i offset ho hv)
  exact hv.trans (load_byte_from_input hm hsize hdisjoint i offset ho)

end
end Ptx.CpAsyncCopyGraph
