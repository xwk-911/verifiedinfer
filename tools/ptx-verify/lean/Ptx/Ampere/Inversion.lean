import Ptx.Ampere.Updates
import Ptx.Ampere.Trace

/-! Invert actual successful source steps. These rules derive type/size facts;
they do not constrain memory values or supply a selected execution witness. -/
namespace Ptx.Ampere
open Ptx.ISA
noncomputable section

theorem bind_success {result : Except ε α} {next : α → Except ε β} {value : β}
    (h : result.bind next = .ok value) : ∃ first, result = .ok first ∧ next first = .ok value := by
  cases result with
  | error error => cases h
  | ok first => exact ⟨first,rfl,h⟩

theorem run_extend_step {ctx oracle code count start mid next head tail}
    (hp : run ctx oracle code count start = .ok (mid,head))
    (hs : step ctx oracle code mid = .ok (next,tail)) :
    run ctx oracle code (count+1) start = .ok (next,head++tail) := by
  rw [run_add,hp]
  simp only [Except.bind,run,hs,List.append_nil]

theorem completed_tail {ctx oracle code count headCount start mid last head allEvents}
    (hr : run ctx oracle code count start = .ok (last,allEvents))
    (hp : run ctx oracle code headCount start = .ok (mid,head)) (hle : headCount ≤ count) :
    ∃ remaining tail, count = headCount+remaining ∧
      run ctx oracle code remaining mid = .ok (last,tail) ∧ allEvents = head++tail := by
  obtain ⟨remaining,hcount⟩ := Nat.exists_eq_add_of_le hle
  rw [hcount,run_add,hp] at hr
  simp only [Except.bind] at hr
  cases ht : run ctx oracle code remaining mid with
  | error fault => simp [ht] at hr
  | ok result =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (by simpa only [ht,Except.bind] using hr))
    exact ⟨remaining,result.2,hcount,ht,rfl⟩

theorem copy_size_of_step {ctx oracle code s next emitted cache dst src size}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.copy cache dst src size))
    (hs : step ctx oracle code s = .ok (next,emitted)) : (oracle.bytes s.scalar.core.queries).length = size := by
  by_cases hc : CopySize cache size
  · cases ha : evalAddr ctx.id.tid.x s.scalar.core.thread src with
    | error fault => simp [step,hr,hi,hc,ha,liftInteger,bind,Except.bind] at hs
    | ok source =>
      cases hb : evalAddr ctx.id.tid.x s.scalar.core.thread dst with
      | error fault => simp [step,hr,hi,hc,ha,hb,liftInteger,bind,Except.bind] at hs
      | ok dest =>
        by_contra hn
        simp [step,hr,hi,hc,ha,hb,hn,liftInteger,bind,Except.bind] at hs
  · simp [step,hr,hi,hc,bind,Except.bind] at hs

def Word32.packedValue : Word32 → Option PackedF16
  | .integer _ => none
  | .packed pair => some pair

@[simp] theorem word_action_pc (s : State) (dst : String) (value : Word32) :
    (wordAction s dst value).scalar.core.thread.pc = s.scalar.core.thread.pc+1 := by cases value <;> rfl
@[simp] theorem word_action_queries (s : State) (dst : String) (value : Word32) :
    (wordAction s dst value).scalar.core.queries = s.scalar.core.queries+1 := by cases value <;> rfl
@[simp] theorem word_action_status (s : State) (dst : String) (value : Word32) :
    (wordAction s dst value).scalar.core.thread.status = s.scalar.core.thread.status := by cases value <;> rfl

theorem word_action_nat_frame (s : State) (dst name : String) (value : Word32) (hn : name ≠ dst) :
    lookup name (wordAction s dst value).scalar.core.thread.regs = lookup name s.scalar.core.thread.regs := by
  cases value with
  | integer value => simp [wordAction,Scalar.finishInteger,assign,Ptx.advance,hn]
  | packed pair => simp [hn]

@[simp] theorem word_action_packed (s : State) (dst name : String) (value : Word32) :
    declarationLookup name (wordAction s dst value).packed =
      if name = dst then value.packedValue else declarationLookup name s.packed := by
  cases value with
  | integer value =>
    simp only [wordAction,Word32.packedValue]
    rw [Scalar.lookup_filter_name name (fun key => key != dst) s.packed]
    by_cases hn : name = dst <;> simp [hn]
  | packed pair => simp [Word32.packedValue]

theorem mma_inputs_of_step {ctx oracle code s next emitted d a b c}
    (hr : s.scalar.core.thread.status = .running)
    (hi : code[s.scalar.core.thread.pc]? = some (.mma d a b c))
    (hs : step ctx oracle code s = .ok (next,emitted)) : ∃ inputs, readMmaInputs s a b c = .ok inputs := by
  by_cases hd : d.names.Nodup
  · cases hinput : readMmaInputs s a b c with
    | error fault => simp [step,hr,hi,hd,hinput,bind,Except.bind] at hs
    | ok inputs => exact ⟨inputs,rfl⟩
  · simp [step,hr,hi,hd,bind,Except.bind] at hs

theorem read_mma_packed {s : State} {a c : Registers4} {b : Registers2} {inputs : MmaInputs}
    (hi : readMmaInputs s a b c = .ok inputs) :
    (∀ i, ∃ pair, declarationLookup (a.get i) s.packed = some pair) ∧
      (∀ i, ∃ pair, declarationLookup (b.get i) s.packed = some pair) := by
  unfold readMmaInputs at hi
  obtain ⟨a0,ha0,hi⟩ := bind_success hi
  obtain ⟨a1,ha1,hi⟩ := bind_success hi
  obtain ⟨a2,ha2,hi⟩ := bind_success hi
  obtain ⟨a3,ha3,hi⟩ := bind_success hi
  obtain ⟨b0,hb0,hi⟩ := bind_success hi
  obtain ⟨b1,hb1,_⟩ := bind_success hi
  have need {name pair} (hh : requirePacked s name = .ok pair) : declarationLookup name s.packed = some pair := by
    cases ht : declarationLookup name s.packed with
    | none => simp [requirePacked,ht] at hh
    | some p => simpa [requirePacked,ht] using hh
  constructor
  · intro i
    fin_cases i
    · exact ⟨a0,need ha0⟩
    · exact ⟨a1,need ha1⟩
    · exact ⟨a2,need ha2⟩
    · exact ⟨a3,need ha3⟩
  · intro i
    fin_cases i
    · exact ⟨b0,need hb0⟩
    · exact ⟨b1,need hb1⟩

end
end Ptx.Ampere
