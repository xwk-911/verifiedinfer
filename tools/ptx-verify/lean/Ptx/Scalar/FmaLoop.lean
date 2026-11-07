import Ptx.Kernels.ScalarMatmulSpec
import Ptx.Scalar.Updates

/-! Relocatable scalar FMA-loop rules for the fixed interpreter. The source
certificate checks every instruction in the eleven-slot fragment. Entry PC and
prior oracle-query count are parameters; code outside the fragment is arbitrary.
Loads remain arbitrary typed replies. Layout/entry/global-memory duties are
separate from these local source-execution rules. -/
namespace Ptx.Scalar.FmaLoop
open Ptx.ISA Ptx.Scalar Ptx.ScalarMatmul
noncomputable section

structure Fragment (code : List Scalar.Instr) (base : Nat) : Prop where
  guard : code[base]? = some (.integer (.setp .ge "%p" (.reg "%k") (.reg "%kmax")))
  branch : code[base+1]? = some (.integer (.branch "%p" true (base+9)))
  loadA : code[base+2]? = some (.load .f32 .global "%av" {base := .reg "%ap"})
  loadB : code[base+3]? = some (.load .f32 .global "%bv" {base := .reg "%bp"})
  fma : code[base+4]? = some (.fmaRn .f32 "%acc" (.reg "%av") (.reg "%bv") (.reg "%acc"))
  advanceA : code[base+5]? = some (.integer (.bin .add 64 64 "%ap" (.reg "%ap") (.imm 4)))
  advanceB : code[base+6]? = some (.integer (.bin .add 64 64 "%bp" (.reg "%bp") (.reg "%stride")))
  advanceK : code[base+7]? = some (.integer (.bin .add 32 32 "%k" (.reg "%k") (.imm 1)))
  back : code[base+8]? = some (.integer (.jump base))
  store : code[base+9]? = some (.store .f32 .global {base := .reg "%cp"} (.reg "%acc"))
  ret : code[base+10]? = some (.integer .ret)

structure Layout where
  count : Nat
  aBase : Nat
  bBase : Nat
  stride : Nat
  output : Nat
  count32 : count < 2^32
  output64 : output < 2^64
  aRead64 : ∀ k, k < count → aBase+4*k < 2^64
  bRead64 : ∀ k, k < count → bBase+stride*k < 2^64

structure Inv (base origin : Nat) (l : Layout) (k : Nat) (acc : ℝ) (s : Scalar.State) : Prop where
  running : s.core.thread.status = .running
  pc : s.core.thread.pc = base
  queries : s.core.queries = origin+2*k
  index : lookup "%k" s.core.thread.regs = some k
  bound : lookup "%kmax" s.core.thread.regs = some l.count
  aPointer : lookup "%ap" s.core.thread.regs = some (wrap 64 (l.aBase+4*k))
  bPointer : lookup "%bp" s.core.thread.regs = some (wrap 64 (l.bBase+l.stride*k))
  stride : lookup "%stride" s.core.thread.regs = some l.stride
  output : lookup "%cp" s.core.thread.regs = some l.output
  accumulator : declarationLookup "%acc" s.floats = some (.f32,acc)
  banks : BanksDisjoint s

def reads (l : Layout) (k : Nat) (a b : ℝ) : List Scalar.Kind := [
  .read ⟨.global,l.aBase+4*k⟩ (Symbolic.encode .f32 a),
  .read ⟨.global,l.bBase+l.stride*k⟩ (Symbolic.encode .f32 b)]

theorem iteration {code : List Scalar.Instr} {base origin : Nat} (fragment : Fragment code base) (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {k : Nat} {acc a b : ℝ} {s : Scalar.State} (hi : Inv base origin l k acc s) (hk : k < l.count)
    (ha : oracle (origin+2*k) = .real .f32 a) (hb : oracle (origin+2*k+1) = .real .f32 b) :
    ∃ next, Scalar.run ctx oracle code 9 s = .ok (next,reads l k a b) ∧ Inv base origin l (k+1) (a*b+acc) next := by
  let s1 := intAssign s "%p" 0
  let s2 := intPC s1 (base+2)
  let s3 := loadedFloat s2 "%av" a
  let s4 := loadedFloat s3 "%bv" b
  let s5 := writeFloat s4 "%acc" .f32 (a*b+acc)
  let s6 := intAssign s5 "%ap" (wrap 64 (l.aBase+4*(k+1)))
  let s7 := intAssign s6 "%bp" (wrap 64 (l.bBase+l.stride*(k+1)))
  let s8 := intAssign s7 "%k" (k+1)
  let s9 := intPC s8 base
  have haccNat := float_value_no_integer hi.banks hi.accumulator
  have hk32 : wrap 32 k = k := Nat.mod_eq_of_lt (by have := l.count32; omega)
  have hK32 : wrap 32 l.count = l.count := Nat.mod_eq_of_lt l.count32
  have hk132 : wrap 32 (k+1) = k+1 := Nat.mod_eq_of_lt (by have := l.count32; omega)
  have hA64 : wrap 64 (l.aBase+4*k) = l.aBase+4*k := Nat.mod_eq_of_lt (l.aRead64 k hk)
  have hB64 : wrap 64 (l.bBase+l.stride*k) = l.bBase+l.stride*k := Nat.mod_eq_of_lt (l.bRead64 k hk)
  have hpA : wrap 64 (wrap 64 (l.aBase+4*k) + wrap 64 4) = wrap 64 (l.aBase+4*(k+1)) := by
    rw [wrap_add]
    congr 1
  have hpB : wrap 64 (wrap 64 (l.bBase+l.stride*k) + wrap 64 l.stride) =
      wrap 64 (l.bBase+l.stride*(k+1)) := by
    rw [wrap_add,Nat.mul_succ]
    congr 1
    omega
  have h32 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply Scalar.integer_local_step hi.running (by rw [hi.pc]; exact fragment.guard) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,hi.index,hi.bound,hk32,hK32,Nat.not_le_of_lt hk,
      bind,Except.bind,pure,Except.pure]
  have h33 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply Scalar.integer_local_step (instruction := .branch "%p" true (base+9)) (by simpa [s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simpa [s1,intAssign,finishInteger,assign,advance,hi.pc] using fragment.branch)
      rfl (by intro bid h; cases h)
    simp [s1,localStep,intAssign,finishInteger,assign,advance,hi.pc,
      bind,Except.bind,pure,Except.pure]
  have h34 : Scalar.step ctx oracle code s2 = .ok (s3,[.read ⟨.global,l.aBase+4*k⟩ (Symbolic.encode .f32 a)]) := by
    apply Scalar.load_step (space := .global) (format := .f32) (dst := "%av")
      (address := {base := .reg "%ap"}) (addr := l.aBase+4*k) (value := a)
    · simpa [s2,s1,intPC,intAssign,finishInteger,assign,advance] using hi.running
    · simpa [s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,assign,advance,hi.pc] using fragment.loadA
    · simp [evalAddr,Ptx.eval,s2,s1,hi.aPointer,hA64,bind,Except.bind,pure,Except.pure]
    · simpa [s2,s1,intPC,intAssign,finishInteger,hi.queries] using ha
  have h35 : Scalar.step ctx oracle code s3 = .ok (s4,[.read ⟨.global,l.bBase+l.stride*k⟩ (Symbolic.encode .f32 b)]) := by
    apply Scalar.load_step (space := .global) (format := .f32) (dst := "%bv")
      (address := {base := .reg "%bp"}) (addr := l.bBase+l.stride*k) (value := b)
    · simpa [s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running
    · simpa [s3,s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,assign,advance,hi.pc] using fragment.loadB
    · simp [evalAddr,Ptx.eval,s3,s2,s1,hi.bPointer,hB64,bind,Except.bind,pure,Except.pure]
    · simpa [s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,hi.queries] using hb
  have h36 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    apply Scalar.fma_step
    · simpa [s4,s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running
    · simpa [s4,s3,s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,assign,advance,hi.pc] using fragment.fma
    · simp [Scalar.eval,Scalar.require,s4,s3,bind,Except.bind,pure,Except.pure]
    · simp [Scalar.eval,Scalar.require,s4,bind,Except.bind,pure,Except.pure]
    · simp [Scalar.eval,Scalar.require,s4,s3,s2,s1,haccNat,hi.accumulator,bind,Except.bind,pure,Except.pure]
  have h37 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    apply Scalar.integer_local_step
      (by simpa [s5,s4,s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running)
      (by simpa [s5,s4,s3,s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,assign,advance,hi.pc] using fragment.advanceA) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s5,s4,s3,s2,s1,hi.aPointer,hpA,
      bind,Except.bind,pure,Except.pure]
  have h38 : Scalar.step ctx oracle code s6 = .ok (s7,[]) := by
    apply Scalar.integer_local_step
      (by simpa [s6,s5,s4,s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running)
      (by simpa [s6,s5,s4,s3,s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,assign,advance,hi.pc] using fragment.advanceB) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s6,s5,s4,s3,s2,s1,hi.bPointer,hi.stride,hpB,
      bind,Except.bind,pure,Except.pure]
  have h39 : Scalar.step ctx oracle code s7 = .ok (s8,[]) := by
    apply Scalar.integer_local_step
      (by simpa [s7,s6,s5,s4,s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running)
      (by simpa [s7,s6,s5,s4,s3,s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,assign,advance,hi.pc] using fragment.advanceK) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s7,s6,s5,s4,s3,s2,s1,hi.index,hk32,hk132,
      show wrap 32 1 = 1 by decide,bind,Except.bind,pure,Except.pure]
  have h40 : Scalar.step ctx oracle code s8 = .ok (s9,[]) := by
    apply Scalar.integer_local_step
      (by simpa [s8,s7,s6,s5,s4,s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running)
      (by simpa [s8,s7,s6,s5,s4,s3,s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,assign,advance,hi.pc] using fragment.back) rfl (by intro bid h; cases h)
    rfl
  have hr : Scalar.run ctx oracle code 9 s = .ok (s9,reads l k a b) := by
    simp [Scalar.run,h32,h33,h34,h35,h36,h37,h38,h39,h40,Except.bind,reads]
  refine ⟨s9,hr,?_⟩
  constructor
  · simpa [s9,s8,s7,s6,s5,s4,s3,s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,assign,advance] using hi.running
  · rfl
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,hi.queries]; omega
  · simp [s9,s8]
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,hi.bound]
  · simp [s9,s8,s7,s6]
  · simp [s9,s8,s7]
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,hi.stride]
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,hi.output]
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1]
  · exact run_banks_disjoint hr hi.banks

structure Finished (base origin : Nat) (l : Layout) (acc : ℝ) (s : Scalar.State) : Prop where
  done : s.core.thread.status = .done
  pc : s.core.thread.pc = base+10
  queries : s.core.queries = origin+2*l.count
  accumulator : declarationLookup "%acc" s.floats = some (.f32,acc)
  output : lookup "%cp" s.core.thread.regs = some l.output
  banks : BanksDisjoint s

theorem finish {code : List Scalar.Instr} {base origin : Nat} (fragment : Fragment code base) (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {acc : ℝ} {s : Scalar.State} (hi : Inv base origin l l.count acc s) :
    ∃ final, Scalar.run ctx oracle code 4 s =
      .ok (final,[.write ⟨.global,l.output⟩ (Symbolic.encode .f32 acc)]) ∧ Finished base origin l acc final := by
  let s1 := intAssign s "%p" 1
  let s2 := intPC s1 (base+9)
  let s3 : Scalar.State := {s2 with core := {s2.core with thread := advance s2.core.thread}}
  let s4 := finishInteger s3 {s3.core with thread := {s3.core.thread with status := .done}}
  have hK32 : wrap 32 l.count = l.count := Nat.mod_eq_of_lt l.count32
  have hout64 : wrap 64 l.output = l.output := Nat.mod_eq_of_lt l.output64
  have haccNat := float_value_no_integer hi.banks hi.accumulator
  have h32 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply Scalar.integer_local_step hi.running (by rw [hi.pc]; exact fragment.guard) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,hi.index,hi.bound,hK32,bind,Except.bind,pure,Except.pure]
  have h33 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply Scalar.integer_local_step (instruction := .branch "%p" true (base+9))
      (by simpa [s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simpa [s1,intAssign,finishInteger,assign,advance,hi.pc] using fragment.branch)
      rfl (by intro bid h; cases h)
    simp [s1,localStep,intAssign,finishInteger,assign,advance,
      bind,Except.bind,pure,Except.pure]
  have h41 : Scalar.step ctx oracle code s2 =
      .ok (s3,[.write ⟨.global,l.output⟩ (Symbolic.encode .f32 acc)]) := by
    apply Scalar.store_step (space := .global) (format := .f32)
      (address := {base := .reg "%cp"}) (value := .reg "%acc") (addr := l.output) (x := acc)
    · simpa [s2,s1,intPC,intAssign,finishInteger,assign,advance] using hi.running
    · simpa [s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,assign,advance,hi.pc] using fragment.store
    · simp [evalAddr,Ptx.eval,s2,s1,hi.output,hout64,bind,Except.bind,pure,Except.pure]
    · simp [Scalar.eval,Scalar.require,s2,s1,haccNat,hi.accumulator,bind,Except.bind,pure,Except.pure]
  have h42 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply Scalar.integer_local_step
      (by simpa [s3,s2,s1,intPC,intAssign,finishInteger,assign,advance] using hi.running)
      (by simpa [s3,s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,assign,advance,hi.pc] using fragment.ret) rfl (by intro bid h; cases h)
    rfl
  have hr : Scalar.run ctx oracle code 4 s =
      .ok (s4,[.write ⟨.global,l.output⟩ (Symbolic.encode .f32 acc)]) := by
    simp [Scalar.run,h32,h33,h41,h42,Except.bind]
  refine ⟨s4,hr,?_⟩
  constructor
  · rfl
  · rfl
  · simpa [s4,s3,s2,s1,intPC,intAssign,finishInteger] using hi.queries
  · simp [s4,finish_integer_lookup,s3,s2,s1,haccNat,hi.accumulator,advance]
  · simpa [s4,finishInteger,s3,advance,s2,s1] using hi.output
  · exact run_banks_disjoint hr hi.banks

def loopReads (l : Layout) (a b : Matrix) (r c start : Nat) : Nat → List Scalar.Kind
  | 0 => []
  | n+1 => reads l start (a r start) (b start c) ++ loopReads l a b r c (start+1) n

@[simp] theorem loopReads_length (l : Layout) (a b : Matrix) (r c start count : Nat) :
    (loopReads l a b r c start count).length = 2*count := by
  induction count generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [loopReads,reads,List.length_append,List.length_cons,List.length_nil,ih]
    omega

theorem loopReads_a {l : Layout} {a b : Matrix} {r c start count i : Nat} (hi : i < count) :
    (loopReads l a b r c start count)[2*i]? =
      some (.read ⟨.global,l.aBase+4*(start+i)⟩ (Symbolic.encode .f32 (a r (start+i)))) := by
  induction count generalizing start i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [loopReads,reads]
    | succ i =>
      have h := ih (start := start+1) (i := i) (by omega)
      have hsum : start+1+i = start+(i+1) := by omega
      simpa only [loopReads,reads,List.cons_append,List.nil_append,Nat.mul_succ,
        Nat.mul_one,List.getElem?_cons_succ,hsum] using h

theorem loopReads_b {l : Layout} {a b : Matrix} {r c start count i : Nat} (hi : i < count) :
    (loopReads l a b r c start count)[2*i+1]? =
      some (.read ⟨.global,l.bBase+l.stride*(start+i)⟩ (Symbolic.encode .f32 (b (start+i) c))) := by
  induction count generalizing start i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [loopReads,reads]
    | succ i =>
      have h := ih (start := start+1) (i := i) (by omega)
      have hsum : start+1+i = start+(i+1) := by omega
      simpa only [loopReads,reads,List.cons_append,List.nil_append,Nat.mul_succ,
        Nat.mul_one,List.getElem?_cons_succ,hsum] using h

theorem loopReads_event {l : Layout} {a b : Matrix} {r c start count serial : Nat} {kind : Scalar.Kind}
    (he : (loopReads l a b r c start count)[serial]? = some kind) :
    ∃ i, i < count ∧
      ((serial = 2*i ∧ kind = .read ⟨.global,l.aBase+4*(start+i)⟩ (Symbolic.encode .f32 (a r (start+i)))) ∨
       (serial = 2*i+1 ∧ kind = .read ⟨.global,l.bBase+l.stride*(start+i)⟩ (Symbolic.encode .f32 (b (start+i) c)))) := by
  have hs := (List.getElem?_eq_some_iff.mp he).1
  rw [loopReads_length] at hs
  have hi : serial/2 < count := by omega
  have hp : serial = 2*(serial/2) ∨ serial = 2*(serial/2)+1 := by omega
  refine ⟨serial/2,hi,?_⟩
  rcases hp with hp | hp
  · left
    refine ⟨hp,?_⟩
    rw [hp,loopReads_a hi] at he
    exact (Option.some.inj he).symm
  · right
    refine ⟨hp,?_⟩
    rw [hp,loopReads_b hi] at he
    exact (Option.some.inj he).symm

/-- The count is derived by induction from remaining iterations. It is not a
chosen fuel cutoff. Replies describe local trace generation only; global memory
reasoning must separately establish that these values are the represented inputs. -/
theorem complete_suffix {code : List Scalar.Instr} {base origin : Nat} (fragment : Fragment code base) (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (a b : Matrix) (r c : Nat)
    (ha : ∀ k, k < l.count → oracle (origin+2*k) = .real .f32 (a r k))
    (hb : ∀ k, k < l.count → oracle (origin+2*k+1) = .real .f32 (b k c))
    (remaining : Nat) :
    ∀ {start s}, l.count = start+remaining → Inv base origin l start (prefixProduct a b r c start) s →
      ∃ final, Scalar.run ctx oracle code (9*remaining+4) s =
        .ok (final,loopReads l a b r c start remaining ++
          [.write ⟨.global,l.output⟩ (Symbolic.encode .f32 (prefixProduct a b r c l.count))]) ∧
        Finished base origin l (prefixProduct a b r c l.count) final := by
  induction remaining with
  | zero =>
    intro start s he hi
    have hstart : start = l.count := by omega
    subst start
    simpa [loopReads] using finish fragment l ctx oracle hi
  | succ n ih =>
    intro start s he hi
    have hk : start < l.count := by omega
    obtain ⟨mid,hr,hm⟩ := iteration fragment l ctx oracle hi hk (ha start hk) (hb start hk)
    change Inv base origin l (start+1) (prefixProduct a b r c (start+1)) mid at hm
    obtain ⟨final,ht,hf⟩ := ih (by omega : l.count = (start+1)+n) hm
    refine ⟨final,?_,hf⟩
    rw [show 9*(n+1)+4 = 9+(9*n+4) by omega,Scalar.run_add,hr]
    simp only [Except.bind,ht,List.append_assoc,loopReads]

theorem complete_from_entry {code : List Scalar.Instr} {base origin : Nat} (fragment : Fragment code base) (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (a b : Matrix) (r c : Nat)
    (ha : ∀ k, k < l.count → oracle (origin+2*k) = .real .f32 (a r k))
    (hb : ∀ k, k < l.count → oracle (origin+2*k+1) = .real .f32 (b k c))
    {s : Scalar.State} (hi : Inv base origin l 0 0 s) :
    ∃ final, Scalar.run ctx oracle code (9*l.count+4) s =
      .ok (final,loopReads l a b r c 0 l.count ++
        [.write ⟨.global,l.output⟩ (Symbolic.encode .f32 (prefixProduct a b r c l.count))]) ∧
      Finished base origin l (prefixProduct a b r c l.count) final :=
  complete_suffix fragment l ctx oracle a b r c ha hb l.count (by omega) hi

end
end Ptx.Scalar.FmaLoop
