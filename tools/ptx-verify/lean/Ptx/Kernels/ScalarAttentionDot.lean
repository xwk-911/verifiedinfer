import Ptx.Generated.ScalarFlashAttention
import Ptx.Kernels.AttentionSpec
import Ptx.Scalar.RegisterFrame

/-! Parametric execution of the ACTUAL generated attention dot loop, PCs 43--51.
Its oracle values remain arbitrary. The local register frame preserves outer-loop
state, while read/memory correspondence and complete kernel execution are separate.
-/
namespace Ptx.ScalarAttentionDot
open Ptx.ISA Ptx.Scalar
noncomputable section
abbrev code := Generated.scalar_flash_attention.program
def changed : List String := ["%p","%qp","%kp","%k","%qv","%kv","%score"]

structure Layout where
  count : Nat
  qBase : Nat
  keyBase : Nat
  firstQuery : Nat
  count32 : count < 2^32
  qRead64 : ∀ k, k < count → qBase+4*k < 2^64
  keyRead64 : ∀ k, k < count → keyBase+4*k < 2^64

structure Inv (l : Layout) (k : Nat) (acc : ℝ) (s : Scalar.State) : Prop where
  running : s.core.thread.status = .running
  pc : s.core.thread.pc = 43
  queries : s.core.queries = l.firstQuery+2*k
  index : lookup "%k" s.core.thread.regs = some k
  bound : lookup "%d" s.core.thread.regs = some l.count
  qPointer : lookup "%qp" s.core.thread.regs = some (wrap 64 (l.qBase+4*k))
  keyPointer : lookup "%kp" s.core.thread.regs = some (wrap 64 (l.keyBase+4*k))
  accumulator : declarationLookup "%score" s.floats = some (.f32,acc)
  banks : BanksDisjoint s

def reads (l : Layout) (k : Nat) (a b : ℝ) : List Scalar.Kind := [
  .read ⟨.global,l.qBase+4*k⟩ (Symbolic.encode .f32 a),
  .read ⟨.global,l.keyBase+4*k⟩ (Symbolic.encode .f32 b)]

theorem iteration (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {k : Nat} {acc a b : ℝ} {s : Scalar.State} (hi : Inv l k acc s) (hk : k < l.count)
    (ha : oracle (l.firstQuery+2*k) = .real .f32 a) (hb : oracle (l.firstQuery+2*k+1) = .real .f32 b) :
    ∃ next, Scalar.run ctx oracle code 9 s = .ok (next,reads l k a b) ∧ Inv l (k+1) (a*b+acc) next ∧ RegisterFrame changed s next := by
  let s1 := intAssign s "%p" 0
  let s2 := intPC s1 45
  let s3 := loadedFloat s2 "%qv" a
  let s4 := loadedFloat s3 "%kv" b
  let s5 := writeFloat s4 "%score" .f32 (a*b+acc)
  let s6 := intAssign s5 "%qp" (wrap 64 (l.qBase+4*(k+1)))
  let s7 := intAssign s6 "%kp" (wrap 64 (l.keyBase+4*(k+1)))
  let s8 := intAssign s7 "%k" (k+1)
  let s9 := intPC s8 43
  have haccNat := float_value_no_integer hi.banks hi.accumulator
  have hk32 : wrap 32 k = k := Nat.mod_eq_of_lt (by have := l.count32; omega)
  have hK32 : wrap 32 l.count = l.count := Nat.mod_eq_of_lt l.count32
  have hk132 : wrap 32 (k+1) = k+1 := Nat.mod_eq_of_lt (by have := l.count32; omega)
  have hA64 : wrap 64 (l.qBase+4*k) = l.qBase+4*k := Nat.mod_eq_of_lt (l.qRead64 k hk)
  have hB64 : wrap 64 (l.keyBase+4*k) = l.keyBase+4*k := Nat.mod_eq_of_lt (l.keyRead64 k hk)
  have hpA : wrap 64 (wrap 64 (l.qBase+4*k) + wrap 64 4) = wrap 64 (l.qBase+4*(k+1)) := by
    rw [wrap_add]
    congr 1
  have hpB : wrap 64 (wrap 64 (l.keyBase+4*k) + wrap 64 4) =
      wrap 64 (l.keyBase+4*(k+1)) := by
    rw [wrap_add]
    congr 1
  have h43 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply Scalar.integer_local_step hi.running (by rw [hi.pc]; rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,hi.index,hi.bound,hk32,hK32,Nat.not_le_of_lt hk,
      bind,Except.bind,pure,Except.pure]
  have h44 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply Scalar.integer_local_step (instruction := .branch "%p" true 52) (by simpa [s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s1,intAssign,finishInteger,assign,advance,hi.pc,code,Generated.scalar_flash_attention.program])
      rfl (by intro bid h; cases h)
    simp [s1,localStep,intAssign,finishInteger,assign,advance,hi.pc,
      bind,Except.bind,pure,Except.pure]
  have h45 : Scalar.step ctx oracle code s2 = .ok (s3,[.read ⟨.global,l.qBase+4*k⟩ (Symbolic.encode .f32 a)]) := by
    apply Scalar.load_step (space := .global) (format := .f32) (dst := "%qv")
      (address := {base := .reg "%qp"}) (addr := l.qBase+4*k) (value := a)
    · simpa [s2,s1,intPC,intAssign,finishInteger,assign,advance] using hi.running
    · rfl
    · simp [evalAddr,Ptx.eval,s2,s1,hi.qPointer,hA64,bind,Except.bind,pure,Except.pure]
    · simpa [s2,s1,intPC,intAssign,finishInteger,hi.queries] using ha
  have h46 : Scalar.step ctx oracle code s3 = .ok (s4,[.read ⟨.global,l.keyBase+4*k⟩ (Symbolic.encode .f32 b)]) := by
    apply Scalar.load_step (space := .global) (format := .f32) (dst := "%kv")
      (address := {base := .reg "%kp"}) (addr := l.keyBase+4*k) (value := b)
    · simpa [s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running
    · rfl
    · simp [evalAddr,Ptx.eval,s3,s2,s1,hi.keyPointer,hB64,bind,Except.bind,pure,Except.pure]
    · simpa [s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,hi.queries] using hb
  have h47 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    apply Scalar.fma_step
    · simpa [s4,s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running
    · rfl
    · simp [Scalar.eval,Scalar.require,s4,s3,bind,Except.bind,pure,Except.pure]
    · simp [Scalar.eval,Scalar.require,s4,bind,Except.bind,pure,Except.pure]
    · simp [Scalar.eval,Scalar.require,s4,s3,s2,s1,haccNat,hi.accumulator,bind,Except.bind,pure,Except.pure]
  have h48 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    apply Scalar.integer_local_step
      (by simpa [s5,s4,s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running)
      (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s5,s4,s3,s2,s1,hi.qPointer,hpA,
      bind,Except.bind,pure,Except.pure]
  have h49 : Scalar.step ctx oracle code s6 = .ok (s7,[]) := by
    apply Scalar.integer_local_step
      (by simpa [s6,s5,s4,s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running)
      (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s6,s5,s4,s3,s2,s1,hi.keyPointer,hpB,
      bind,Except.bind,pure,Except.pure]
  have h50 : Scalar.step ctx oracle code s7 = .ok (s8,[]) := by
    apply Scalar.integer_local_step
      (by simpa [s7,s6,s5,s4,s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running)
      (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s7,s6,s5,s4,s3,s2,s1,hi.index,hk32,hk132,
      show wrap 32 1 = 1 by decide,bind,Except.bind,pure,Except.pure]
  have h51 : Scalar.step ctx oracle code s8 = .ok (s9,[]) := by
    apply Scalar.integer_local_step
      (by simpa [s8,s7,s6,s5,s4,s3,s2,s1,loadedFloat,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running)
      (by rfl) rfl (by intro bid h; cases h)
    rfl
  have hr : Scalar.run ctx oracle code 9 s = .ok (s9,reads l k a b) := by
    simp [Scalar.run,h43,h44,h45,h46,h47,h48,h49,h50,h51,Except.bind,reads]
  have hb2 : BanksDisjoint s2 := intPC_banks _ _
  have hb3 : BanksDisjoint s3 := loadedFloat_banks hb2 _ _
  have hb4 : BanksDisjoint s4 := loadedFloat_banks hb3 _ _
  have hb5 : BanksDisjoint s5 := write_float_disjoint hb4 _ _ _
  have hf : RegisterFrame changed s s9 := by
    apply register_frame_trans (intAssign_register_frame hi.banks "%p" 0 (by decide))
    apply register_frame_trans (intPC_register_frame (intAssign_banks _ _ _) 45)
    apply register_frame_trans (loadedFloat_register_frame s2 "%qv" a (by decide))
    apply register_frame_trans (loadedFloat_register_frame s3 "%kv" b (by decide))
    apply register_frame_trans (writeFloat_register_frame s4 "%score" .f32 (a*b+acc) (by decide))
    apply register_frame_trans (intAssign_register_frame hb5 "%qp" _ (by decide))
    apply register_frame_trans (intAssign_register_frame (intAssign_banks _ _ _) "%kp" _ (by decide))
    apply register_frame_trans (intAssign_register_frame (intAssign_banks _ _ _) "%k" _ (by decide))
    exact intPC_register_frame (intAssign_banks _ _ _) 43
  refine ⟨s9,hr,?_,hf⟩
  constructor
  · simpa [s9,s8,s7,s6,s5,s4,s3,s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,assign,advance] using hi.running
  · rfl
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,intPC,intAssign,loadedFloat,writeFloat,finishInteger,hi.queries]; omega
  · simp [s9,s8]
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,hi.bound]
  · simp [s9,s8,s7,s6]
  · simp [s9,s8,s7]
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1]
  · exact run_banks_disjoint hr hi.banks

structure Finished (l : Layout) (acc : ℝ) (s : Scalar.State) : Prop where
  running : s.core.thread.status = .running
  pc : s.core.thread.pc = 52
  queries : s.core.queries = l.firstQuery+2*l.count
  qPointer : lookup "%qp" s.core.thread.regs = some (wrap 64 (l.qBase+4*l.count))
  keyPointer : lookup "%kp" s.core.thread.regs = some (wrap 64 (l.keyBase+4*l.count))
  accumulator : declarationLookup "%score" s.floats = some (.f32,acc)
  banks : BanksDisjoint s

theorem finish (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {acc : ℝ} {s : Scalar.State} (hi : Inv l l.count acc s) :
    ∃ final, Scalar.run ctx oracle code 2 s = .ok (final,[]) ∧
      Finished l acc final ∧ RegisterFrame changed s final := by
  let s1 := intAssign s "%p" 1
  let s2 := intPC s1 52
  have hK32 : wrap 32 l.count = l.count := Nat.mod_eq_of_lt l.count32
  have haccNat := float_value_no_integer hi.banks hi.accumulator
  have h43 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply Scalar.integer_local_step hi.running (by rw [hi.pc]; rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,hi.index,hi.bound,hK32,bind,Except.bind,pure,Except.pure]
  have h44 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply Scalar.integer_local_step (instruction := .branch "%p" true 52)
      (by simpa [s1,intAssign,finishInteger,assign,advance] using hi.running)
      (by simp [s1,intAssign,finishInteger,assign,advance,hi.pc,code,Generated.scalar_flash_attention.program])
      rfl (by intro bid h; cases h)
    simp [s1,localStep,intAssign,finishInteger,assign,advance,bind,Except.bind,pure,Except.pure]
  have hr : Scalar.run ctx oracle code 2 s = .ok (s2,[]) := by
    simp [Scalar.run,h43,h44,Except.bind]
  have hf : RegisterFrame changed s s2 := register_frame_trans
    (intAssign_register_frame hi.banks "%p" 1 (by decide))
    (intPC_register_frame (intAssign_banks _ _ _) 52)
  refine ⟨s2,hr,?_,hf⟩
  constructor
  · simpa [s2,s1,intPC,intAssign,finishInteger,assign,advance] using hi.running
  · rfl
  · simpa [s2,s1,intPC,intAssign,finishInteger] using hi.queries
  · simpa [s2,s1] using hi.qPointer
  · simpa [s2,s1] using hi.keyPointer
  · simp [s2,s1,haccNat,hi.accumulator]
  · exact run_banks_disjoint hr hi.banks

def dotPrefix (a b : Nat → ℝ) : Nat → ℝ
  | 0 => 0
  | k+1 => a k*b k+dotPrefix a b k

theorem prefix_attention (q key : Attention.Matrix) (row item count : Nat) :
    dotPrefix (q row) (key item) count = Attention.dot q key row item count := by
  induction count with
  | zero => rfl
  | succ k ih => simp only [dotPrefix,Attention.dot,ih]

def loopReads (l : Layout) (a b : Nat → ℝ) (start : Nat) : Nat → List Scalar.Kind
  | 0 => []
  | n+1 => reads l start (a start) (b start) ++ loopReads l a b (start+1) n

@[simp] theorem loopReads_length (l : Layout) (a b : Nat → ℝ) (start count : Nat) :
    (loopReads l a b start count).length = 2*count := by
  induction count generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [loopReads,reads,List.length_append,List.length_cons,List.length_nil,ih]
    omega

theorem loopReads_q {l : Layout} {a b : Nat → ℝ} {start count i : Nat} (hi : i < count) :
    (loopReads l a b start count)[2*i]? =
      some (.read ⟨.global,l.qBase+4*(start+i)⟩ (Symbolic.encode .f32 (a (start+i)))) := by
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

theorem loopReads_key {l : Layout} {a b : Nat → ℝ} {start count i : Nat} (hi : i < count) :
    (loopReads l a b start count)[2*i+1]? =
      some (.read ⟨.global,l.keyBase+4*(start+i)⟩ (Symbolic.encode .f32 (b (start+i)))) := by
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

theorem loopReads_event {l : Layout} {a b : Nat → ℝ} {start count serial : Nat} {kind : Scalar.Kind}
    (he : (loopReads l a b start count)[serial]? = some kind) :
    ∃ i, i < count ∧
      ((serial = 2*i ∧ kind = .read ⟨.global,l.qBase+4*(start+i)⟩ (Symbolic.encode .f32 (a (start+i)))) ∨
       (serial = 2*i+1 ∧ kind = .read ⟨.global,l.keyBase+4*(start+i)⟩ (Symbolic.encode .f32 (b (start+i))))) := by
  have hs := (List.getElem?_eq_some_iff.mp he).1
  rw [loopReads_length] at hs
  have hi : serial/2 < count := by omega
  have hp : serial = 2*(serial/2) ∨ serial = 2*(serial/2)+1 := by omega
  refine ⟨serial/2,hi,?_⟩
  rcases hp with hp | hp
  · left
    refine ⟨hp,?_⟩
    rw [hp,loopReads_q hi] at he
    exact (Option.some.inj he).symm
  · right
    refine ⟨hp,?_⟩
    rw [hp,loopReads_key hi] at he
    exact (Option.some.inj he).symm

/-- The instruction count is derived from remaining loop iterations. Query
offsets are arbitrary, and the unused one-past pointers retain u64 wrapping. -/
theorem complete_suffix (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (a b : Nat → ℝ)
    (ha : ∀ k, k < l.count → oracle (l.firstQuery+2*k) = .real .f32 (a k))
    (hb : ∀ k, k < l.count → oracle (l.firstQuery+2*k+1) = .real .f32 (b k))
    (remaining : Nat) :
    ∀ {start s}, l.count = start+remaining → Inv l start (dotPrefix a b start) s →
      ∃ final, Scalar.run ctx oracle code (9*remaining+2) s =
        .ok (final,loopReads l a b start remaining) ∧
        Finished l (dotPrefix a b l.count) final ∧ RegisterFrame changed s final := by
  induction remaining with
  | zero =>
    intro start s he hi
    have hstart : start = l.count := by omega
    subst start
    simpa [loopReads] using finish l ctx oracle hi
  | succ n ih =>
    intro start s he hi
    have hk : start < l.count := by omega
    obtain ⟨mid,hr,hm,hframe⟩ := iteration l ctx oracle hi hk (ha start hk) (hb start hk)
    change Inv l (start+1) (dotPrefix a b (start+1)) mid at hm
    obtain ⟨final,ht,hf,hrest⟩ := ih (by omega : l.count = (start+1)+n) hm
    refine ⟨final,?_,hf,register_frame_trans hframe hrest⟩
    rw [show 9*(n+1)+2 = 9+(9*n+2) by omega,Scalar.run_add,hr]
    simp only [Except.bind,ht,loopReads]

theorem complete_from_entry (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (a b : Nat → ℝ)
    (ha : ∀ k, k < l.count → oracle (l.firstQuery+2*k) = .real .f32 (a k))
    (hb : ∀ k, k < l.count → oracle (l.firstQuery+2*k+1) = .real .f32 (b k))
    {s : Scalar.State} (hi : Inv l 0 0 s) :
    ∃ final, Scalar.run ctx oracle code (9*l.count+2) s = .ok (final,loopReads l a b 0 l.count) ∧
      Finished l (dotPrefix a b l.count) final ∧ RegisterFrame changed s final :=
  complete_suffix l ctx oracle a b ha hb l.count (by omega) hi

theorem complete_attention_dot (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (q key : Attention.Matrix) (row item : Nat)
    (ha : ∀ k, k < l.count → oracle (l.firstQuery+2*k) = .real .f32 (q row k))
    (hb : ∀ k, k < l.count → oracle (l.firstQuery+2*k+1) = .real .f32 (key item k))
    {s : Scalar.State} (hi : Inv l 0 0 s) :
    ∃ final, Scalar.run ctx oracle code (9*l.count+2) s = .ok (final,loopReads l (q row) (key item) 0 l.count) ∧
      Finished l (Attention.dot q key row item l.count) final ∧ RegisterFrame changed s final := by
  simpa only [prefix_attention] using complete_from_entry l ctx oracle (q row) (key item) ha hb hi

structure Scored (l : Layout) (score : ℝ) (s : Scalar.State) : Prop where
  running : s.core.thread.status = .running
  pc : s.core.thread.pc = 53
  queries : s.core.queries = l.firstQuery+2*l.count
  keyPointer : lookup "%kp" s.core.thread.regs = some (wrap 64 (l.keyBase+4*l.count))
  scoreValue : declarationLookup "%score" s.floats = some (.f32,score)
  banks : BanksDisjoint s

theorem complete_scaled_score (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (q key : Attention.Matrix) (row item : Nat) (scale : ℝ)
    (ha : ∀ k, k < l.count → oracle (l.firstQuery+2*k) = .real .f32 (q row k))
    (hb : ∀ k, k < l.count → oracle (l.firstQuery+2*k+1) = .real .f32 (key item k))
    {s : Scalar.State} (hi : Inv l 0 0 s)
    (hscale : declarationLookup "%scale" s.floats = some (.f32,scale)) :
    ∃ final, Scalar.run ctx oracle code (9*l.count+3) s = .ok (final,loopReads l (q row) (key item) 0 l.count) ∧
      Scored l (scale*Attention.dot q key row item l.count) final ∧ RegisterFrame changed s final := by
  obtain ⟨mid,hr,hm,hframe⟩ := complete_attention_dot l ctx oracle q key row item ha hb hi
  let result := scale*Attention.dot q key row item l.count
  let final := writeFloat mid "%score" .f32 result
  have hs : declarationLookup "%scale" mid.floats = some (.f32,scale) :=
    ((hframe "%scale" (by decide)).2).trans hscale
  have h52 : Scalar.step ctx oracle code mid = .ok (final,[]) := by
    apply mul_float_step hm.running (by rw [hm.pc]; rfl)
    · simp [Scalar.eval,require,hs,bind,Except.bind,pure,Except.pure]
    · simp [Scalar.eval,require,hm.accumulator,bind,Except.bind,pure,Except.pure]
  have hout : Scalar.run ctx oracle code (9*l.count+3) s =
      .ok (final,loopReads l (q row) (key item) 0 l.count) := by
    rw [show 9*l.count+3 = (9*l.count+2)+1 by omega,Scalar.run_add,hr]
    simp [Scalar.run,h52,Except.bind]
  refine ⟨final,hout,?_,register_frame_trans hframe (writeFloat_register_frame mid "%score" .f32 result (by decide))⟩
  constructor
  · simpa [final,writeFloat,advance] using hm.running
  · simp [final,writeFloat,advance,hm.pc]
  · exact hm.queries
  · simpa [final] using hm.keyPointer
  · exact float_write_lookup _ _ _ _
  · exact write_float_disjoint hm.banks _ _ _

end
end Ptx.ScalarAttentionDot
