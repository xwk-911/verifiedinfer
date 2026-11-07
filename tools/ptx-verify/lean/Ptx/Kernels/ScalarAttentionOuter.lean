import Ptx.Kernels.ScalarAttentionDot
import Ptx.Kernels.ScalarAttentionOuterUpdate
import Ptx.Scalar.Control

/-! Source-local outer-loop composition for scalar online attention. The layout
and reply hypotheses describe a selected execution. They do not prove global
memory consistency, initial-read correspondence or physical allocation safety. -/
namespace Ptx.ScalarAttentionOuter
open Ptx.ISA Ptx.Scalar
noncomputable section
abbrev code := Generated.scalar_flash_attention.program

structure Layout where
  keys : Nat
  dim : Nat
  qBase : Nat
  keyBase : Nat
  valueBase : Nat
  output : Nat
  firstQuery : Nat
  keys32 : keys < 2^32
  dim32 : dim < 2^32
  output64 : output < 2^64
  qRead64 : ∀ k, k < dim → qBase+4*k < 2^64
  keyRead64 : ∀ j k, j < keys → k < dim → keyBase+4*dim*j+4*k < 2^64
  valueRead64 : ∀ j, j < keys → valueBase+4*dim*j < 2^64

def queryIndex (l : Layout) (j : Nat) : Nat := l.firstQuery+(2*l.dim+1)*j
def dotLayout (l : Layout) (j : Nat) (hj : j < l.keys) : ScalarAttentionDot.Layout := {
  count := l.dim, qBase := l.qBase, keyBase := l.keyBase+4*l.dim*j, firstQuery := queryIndex l j
  count32 := l.dim32
  qRead64 := l.qRead64
  keyRead64 := fun k hk => l.keyRead64 j k hj hk
}
def scores (l : Layout) (q key : Attention.Matrix) (scale : ℝ) (row : Nat) (j : Nat) : ℝ :=
  scale*Attention.dot q key row j l.dim

structure Inv (l : Layout) (score value : Nat → ℝ) (scale : ℝ) (j : Nat) (s : Scalar.State) : Prop where
  running : s.core.thread.status = .running
  pc : s.core.thread.pc = 37
  queries : s.core.queries = queryIndex l j
  index : lookup "%j" s.core.thread.regs = some j
  keyCount : lookup "%n" s.core.thread.regs = some l.keys
  dimension : lookup "%d" s.core.thread.regs = some l.dim
  qRow : lookup "%qr" s.core.thread.regs = some (wrap 64 l.qBase)
  keyRow : lookup "%kr" s.core.thread.regs = some (wrap 64 (l.keyBase+4*l.dim*j))
  valuePointer : lookup "%vp" s.core.thread.regs = some (wrap 64 (l.valueBase+4*l.dim*j))
  stride : lookup "%stride" s.core.thread.regs = some (4*l.dim)
  output : lookup "%op" s.core.thread.regs = some l.output
  scaling : declarationLookup "%scale" s.floats = some (.f32,scale)
  online : j ≠ 0 → ScalarAttentionUpdate.Registers s (OnlineSoftmax.run score value j)
  banks : BanksDisjoint s

theorem start_dot (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {score value scale j s} (hi : Inv l score value scale j s) (hj : j < l.keys) :
    ∃ ready, Scalar.run ctx oracle code 6 s = .ok (ready,[]) ∧
      ScalarAttentionDot.Inv (dotLayout l j hj) 0 0 ready ∧
      RegisterFrame ScalarAttentionDot.changed s ready := by
  let s1 := intAssign s "%p" 0
  let s2 := intPC s1 39
  let s3 := intAssign s2 "%qp" (wrap 64 l.qBase)
  let s4 := intAssign s3 "%kp" (wrap 64 (l.keyBase+4*l.dim*j))
  let s5 := intAssign s4 "%k" 0
  let s6 := writeFloat s5 "%score" .f32 0
  have hj32 : j < 2^32 := lt_trans hj l.keys32
  have h37 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply integer_local_step hi.running (by rw [hi.pc]; rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,hi.index,hi.keyCount,
      show wrap 32 j = j from Nat.mod_eq_of_lt hj32,
      show wrap 32 l.keys = l.keys from Nat.mod_eq_of_lt l.keys32,Nat.not_le_of_lt hj,
      bind,Except.bind,pure,Except.pure]
  have h38 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply integer_local_step (instruction := .branch "%p" true 73)
      (by simpa [s1,intAssign,finishInteger,assign,Ptx.advance] using hi.running)
      (by simp [s1,intAssign,finishInteger,assign,advance,hi.pc,code,Generated.scalar_flash_attention.program])
      rfl (by intro bid h; cases h)
    simp [localStep,s1,intAssign,finishInteger,assign,advance,hi.pc,bind,Except.bind,pure,Except.pure]
  have h39 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply integer_local_step
      (by simpa [s2,s1,intPC,intAssign,finishInteger,assign,advance] using hi.running)
      (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s2,s1,hi.qRow,bind,Except.bind,pure,Except.pure]
  have h40 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply integer_local_step
      (by simpa [s3,s2,s1,intPC,intAssign,finishInteger,assign,advance] using hi.running)
      (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s3,s2,s1,hi.keyRow,bind,Except.bind,pure,Except.pure]
  have h41 : Scalar.step ctx oracle code s4 = .ok (s5,[]) := by
    apply integer_local_step
      (by simpa [s4,s3,s2,s1,intPC,intAssign,finishInteger,assign,advance] using hi.running)
      (by rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,show wrap 32 0 = 0 by decide,bind,Except.bind,pure,Except.pure]
  have h42 : Scalar.step ctx oracle code s5 = .ok (s6,[]) := by
    apply mov_float_step
    · simpa [s5,s4,s3,s2,s1,intPC,intAssign,finishInteger,assign,advance] using hi.running
    · rfl
    · simp [Scalar.eval]
  have hr : Scalar.run ctx oracle code 6 s = .ok (s6,[]) := by
    simp [Scalar.run,h37,h38,h39,h40,h41,h42,Except.bind]
  have hf : RegisterFrame ScalarAttentionDot.changed s s6 := by
    apply register_frame_trans (intAssign_register_frame hi.banks "%p" 0 (by decide))
    apply register_frame_trans (intPC_register_frame (intAssign_banks _ _ _) 39)
    apply register_frame_trans (intAssign_register_frame (intPC_banks _ _) "%qp" _ (by decide))
    apply register_frame_trans (intAssign_register_frame (intAssign_banks _ _ _) "%kp" _ (by decide))
    apply register_frame_trans (intAssign_register_frame (intAssign_banks _ _ _) "%k" _ (by decide))
    exact writeFloat_register_frame _ "%score" .f32 _ (by decide)
  refine ⟨s6,hr,?_,hf⟩
  constructor
  · simpa [s6,s5,s4,s3,s2,s1,writeFloat,intPC,intAssign,finishInteger,assign,advance] using hi.running
  · rfl
  · simpa [s6,s5,s4,s3,s2,s1,writeFloat,intPC,intAssign,finishInteger,dotLayout] using hi.queries
  · simp [s6,s5]
  · exact (hf "%d" (by decide)).1.trans hi.dimension
  · simp [s6,s5,s4,s3,dotLayout]
  · simp [s6,s5,s4,dotLayout]
  · exact float_write_lookup _ _ _ _
  · exact run_banks_disjoint hr hi.banks

structure Next (l : Layout) (score value : Nat → ℝ) (scale : ℝ) (j : Nat) (s : Scalar.State) : Prop where
  running : s.core.thread.status = .running
  pc : s.core.thread.pc = 69
  queries : s.core.queries = queryIndex l (j+1)
  index : lookup "%j" s.core.thread.regs = some j
  keyCount : lookup "%n" s.core.thread.regs = some l.keys
  dimension : lookup "%d" s.core.thread.regs = some l.dim
  qRow : lookup "%qr" s.core.thread.regs = some (wrap 64 l.qBase)
  keyNext : lookup "%kp" s.core.thread.regs = some (wrap 64 (l.keyBase+4*l.dim*(j+1)))
  valuePointer : lookup "%vp" s.core.thread.regs = some (wrap 64 (l.valueBase+4*l.dim*j))
  stride : lookup "%stride" s.core.thread.regs = some (4*l.dim)
  output : lookup "%op" s.core.thread.regs = some l.output
  scaling : declarationLookup "%scale" s.floats = some (.f32,scale)
  online : ScalarAttentionUpdate.Registers s (OnlineSoftmax.run score value (j+1))
  banks : BanksDisjoint s

theorem advance (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    {score value scale j s} (hi : Next l score value scale j s) (hj : j < l.keys) :
    ∃ next, Scalar.run ctx oracle code 4 s = .ok (next,[]) ∧
      Inv l score value scale (j+1) next ∧ RegisterFrame ["%kr","%vp","%j"] s next := by
  let s1 := intAssign s "%kr" (wrap 64 (l.keyBase+4*l.dim*(j+1)))
  let s2 := intAssign s1 "%vp" (wrap 64 (l.valueBase+4*l.dim*(j+1)))
  let s3 := intAssign s2 "%j" (j+1)
  let s4 := intPC s3 37
  have hj32 : wrap 32 j = j := Nat.mod_eq_of_lt (lt_trans hj l.keys32)
  have hj132 : wrap 32 (j+1) = j+1 := Nat.mod_eq_of_lt (by have := l.keys32; omega)
  have hstride64 : wrap 64 (4*l.dim) = 4*l.dim := Nat.mod_eq_of_lt (by have := l.dim32; omega)
  have hvp : wrap 64 (wrap 64 (l.valueBase+4*l.dim*j)+wrap 64 (4*l.dim)) =
      wrap 64 (l.valueBase+4*l.dim*(j+1)) := by
    rw [wrap_add,Nat.mul_succ]
    congr 1
    omega
  have h69 : Scalar.step ctx oracle code s = .ok (s1,[]) := by
    apply integer_local_step hi.running (by rw [hi.pc]; rfl) rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,hi.keyNext,bind,Except.bind,pure,Except.pure]
  have h70 : Scalar.step ctx oracle code s1 = .ok (s2,[]) := by
    apply integer_local_step
      (by simpa [s1,intAssign,finishInteger,assign,Ptx.advance] using hi.running)
      (by simp only [s1,intAssign,finishInteger,assign,Ptx.advance,hi.pc]; rfl)
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s1,hi.valuePointer,hi.stride,hvp,bind,Except.bind,pure,Except.pure]
  have h71 : Scalar.step ctx oracle code s2 = .ok (s3,[]) := by
    apply integer_local_step
      (by simpa [s2,s1,intAssign,finishInteger,assign,Ptx.advance] using hi.running)
      (by simp only [s2,s1,intAssign,finishInteger,assign,Ptx.advance,hi.pc]; rfl)
      rfl (by intro bid h; cases h)
    simp [localStep,Ptx.eval,s2,s1,hi.index,hj32,hj132,show wrap 32 1 = 1 by decide,
      bind,Except.bind,pure,Except.pure]
  have h72 : Scalar.step ctx oracle code s3 = .ok (s4,[]) := by
    apply integer_local_step
      (by simpa [s3,s2,s1,intAssign,finishInteger,assign,Ptx.advance] using hi.running)
      (by simp only [s3,s2,s1,intAssign,finishInteger,assign,Ptx.advance,hi.pc]; rfl)
      rfl (by intro bid h; cases h)
    rfl
  have hr : Scalar.run ctx oracle code 4 s = .ok (s4,[]) := by
    simp [Scalar.run,h69,h70,h71,h72,Except.bind]
  have hf : RegisterFrame ["%kr","%vp","%j"] s s4 := by
    apply register_frame_trans (intAssign_register_frame hi.banks "%kr" _ (by decide))
    apply register_frame_trans (intAssign_register_frame (intAssign_banks _ _ _) "%vp" _ (by decide))
    apply register_frame_trans (intAssign_register_frame (intAssign_banks _ _ _) "%j" _ (by decide))
    exact intPC_register_frame (intAssign_banks _ _ _) 37
  refine ⟨s4,hr,?_,hf⟩
  constructor
  · simpa [s4,s3,s2,s1,intPC,intAssign,finishInteger,assign,Ptx.advance] using hi.running
  · rfl
  · simpa [s4,s3,s2,s1,intPC,intAssign,finishInteger] using hi.queries
  · simp [s4,s3]
  · exact ((hf "%n" (by decide)).1).trans hi.keyCount
  · exact ((hf "%d" (by decide)).1).trans hi.dimension
  · exact ((hf "%qr" (by decide)).1).trans hi.qRow
  · simp [s4,s3,s2,s1]
  · simp [s4,s3,s2]
  · exact ((hf "%stride" (by decide)).1).trans hi.stride
  · exact ((hf "%op" (by decide)).1).trans hi.output
  · exact ((hf "%scale" (by decide)).2).trans hi.scaling
  · intro _
    exact ⟨((hf "%max" (by decide)).2).trans hi.online.1,
      ((hf "%l" (by decide)).2).trans hi.online.2.1,((hf "%u" (by decide)).2).trans hi.online.2.2⟩
  · exact run_banks_disjoint hr hi.banks

def changed : List String := ["%p","%qp","%kp","%k","%qv","%kv","%score","%vv",
  "%nextm","%a","%w","%max","%l","%u","%kr","%vp","%j"]
def iterationSteps (dim j : Nat) : Nat := 9*dim+(if j = 0 then 19 else 26)
def iterationReads (l : Layout) (q key value : Attention.Matrix) (row col j : Nat) (hj : j < l.keys) : List Scalar.Kind :=
  ScalarAttentionDot.loopReads (dotLayout l j hj) (q row) (key j) 0 l.dim ++
    [.read ⟨.global,l.valueBase+4*l.dim*j⟩ (Symbolic.encode .f32 (value j col))]

theorem iteration_for_score (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (q key value : Attention.Matrix) (row col : Nat) (scale : ℝ) (score : Nat → ℝ) {j s}
    (hi : Inv l score (fun item => value item col) scale j s) (hj : j < l.keys)
    (hscore : score j = scale*Attention.dot q key row j l.dim)
    (hq : ∀ k, k < l.dim → oracle (queryIndex l j+2*k) = .real .f32 (q row k))
    (hk : ∀ k, k < l.dim → oracle (queryIndex l j+2*k+1) = .real .f32 (key j k))
    (hv : oracle (queryIndex l j+2*l.dim) = .real .f32 (value j col)) :
    ∃ next, Scalar.run ctx oracle code (iterationSteps l.dim j) s = .ok (next,iterationReads l q key value row col j hj) ∧
      Inv l score (fun item => value item col) scale (j+1) next ∧ RegisterFrame changed s next := by
  obtain ⟨ready,hstart,hready,hstartFrame⟩ := start_dot l ctx oracle hi hj
  have hscale : declarationLookup "%scale" ready.floats = some (.f32,scale) :=
    ((hstartFrame "%scale" (by decide)).2).trans hi.scaling
  obtain ⟨scored,hdot,hscored,hdotFrame⟩ := ScalarAttentionDot.complete_scaled_score
    (dotLayout l j hj) ctx oracle q key row j scale hq hk hready hscale
  change Scalar.run ctx oracle code (9*l.dim+3) ready =
    .ok (scored,ScalarAttentionDot.loopReads (dotLayout l j hj) (q row) (key j) 0 l.dim) at hdot
  have hthrough : RegisterFrame ScalarAttentionDot.changed s scored := register_frame_trans hstartFrame hdotFrame
  have hindex : lookup "%j" scored.core.thread.regs = some j :=
    ((hthrough "%j" (by decide)).1).trans hi.index
  have hpointer : lookup "%vp" scored.core.thread.regs = some (wrap 64 (l.valueBase+4*l.dim*j)) :=
    ((hthrough "%vp" (by decide)).1).trans hi.valuePointer
  have honline : j ≠ 0 → ScalarAttentionUpdate.Registers scored
      (OnlineSoftmax.run score (fun item => value item col) j) := by
    intro hz
    obtain ⟨hm,hl,hu⟩ := hi.online hz
    exact ⟨((hthrough "%max" (by decide)).2).trans hm,
      ((hthrough "%l" (by decide)).2).trans hl,((hthrough "%u" (by decide)).2).trans hu⟩
  have hanswer : oracle scored.core.queries = .real .f32 (value j col) := by
    simpa only [hscored.queries,dotLayout] using hv
  obtain ⟨updated,hupdate,hu,hupdateFrame⟩ := ScalarAttentionOuterUpdate.value_and_update ctx oracle
    score (fun item => value item col) j (l.valueBase+4*l.dim*j) scored
    hscored.running hscored.pc (lt_trans hj l.keys32) (l.valueRead64 j hj) hindex hpointer
    (by simpa only [hscore,show (dotLayout l j hj).count = l.dim from rfl] using hscored.scoreValue)
    honline hscored.banks hanswer
  change Scalar.run ctx oracle code (if j = 0 then 6 else 13) scored =
    .ok (updated,[.read ⟨.global,l.valueBase+4*l.dim*j⟩ (Symbolic.encode .f32 (value j col))]) at hupdate
  have hnext : Next l score (fun item => value item col) scale j updated := by
    constructor
    · exact hu.running
    · exact hu.pc
    · rw [hu.queries,hscored.queries]
      simp only [dotLayout,queryIndex,Nat.mul_succ]
      omega
    · exact ((hupdateFrame "%j" (by decide)).1).trans hindex
    · exact ((hupdateFrame "%n" (by decide)).1).trans (((hthrough "%n" (by decide)).1).trans hi.keyCount)
    · exact ((hupdateFrame "%d" (by decide)).1).trans (((hthrough "%d" (by decide)).1).trans hi.dimension)
    · exact ((hupdateFrame "%qr" (by decide)).1).trans (((hthrough "%qr" (by decide)).1).trans hi.qRow)
    · have hp := ((hupdateFrame "%kp" (by decide)).1).trans hscored.keyPointer
      simpa only [dotLayout,Nat.mul_succ,Nat.add_assoc] using hp
    · exact ((hupdateFrame "%vp" (by decide)).1).trans hpointer
    · exact ((hupdateFrame "%stride" (by decide)).1).trans (((hthrough "%stride" (by decide)).1).trans hi.stride)
    · exact ((hupdateFrame "%op" (by decide)).1).trans (((hthrough "%op" (by decide)).1).trans hi.output)
    · exact ((hupdateFrame "%scale" (by decide)).2).trans (((hthrough "%scale" (by decide)).2).trans hi.scaling)
    · exact hu.online
    · exact hu.banks
  obtain ⟨next,hadvance,hfinal,hadvanceFrame⟩ := advance l ctx oracle hnext hj
  have hcount : iterationSteps l.dim j = 6+((9*l.dim+3)+((if j = 0 then 6 else 13)+4)) := by
    by_cases hz : j = 0 <;> simp [iterationSteps,hz] <;> omega
  have hrun : Scalar.run ctx oracle code (iterationSteps l.dim j) s =
      .ok (next,iterationReads l q key value row col j hj) := by
    rw [hcount,Scalar.run_add,hstart]
    simp only [Except.bind,List.nil_append]
    rw [Scalar.run_add,hdot]
    simp only [Except.bind]
    rw [Scalar.run_add,hupdate]
    simp only [Except.bind,hadvance,List.append_nil,iterationReads]
  have hframe : RegisterFrame changed s next := register_frame_trans
    (register_frame_mono hthrough (by simp [List.Subset,ScalarAttentionDot.changed,changed]))
    (register_frame_trans
      (register_frame_mono hupdateFrame (by simp [List.Subset,ScalarAttentionOuterUpdate.changed,changed]))
      (register_frame_mono hadvanceFrame (by simp [List.Subset,changed])))
  exact ⟨next,hrun,hfinal,hframe⟩

theorem iteration (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (q key value : Attention.Matrix) (row col : Nat) (scale : ℝ) {j s}
    (hi : Inv l (scores l q key scale row) (fun item => value item col) scale j s) (hj : j < l.keys)
    (hq : ∀ k, k < l.dim → oracle (queryIndex l j+2*k) = .real .f32 (q row k))
    (hk : ∀ k, k < l.dim → oracle (queryIndex l j+2*k+1) = .real .f32 (key j k))
    (hv : oracle (queryIndex l j+2*l.dim) = .real .f32 (value j col)) :
    ∃ next, Scalar.run ctx oracle code (iterationSteps l.dim j) s = .ok (next,iterationReads l q key value row col j hj) ∧
      Inv l (scores l q key scale row) (fun item => value item col) scale (j+1) next ∧ RegisterFrame changed s next :=
  iteration_for_score l ctx oracle q key value row col scale (scores l q key scale row) hi hj rfl hq hk hv

theorem finish (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (score value : Nat → ℝ) (scale : ℝ) (hkeys : 0 < l.keys) {s}
    (hi : Inv l score value scale l.keys s) :
    ∃ final, Scalar.run ctx oracle code 5 s = .ok
      (final,[.write ⟨.global,l.output⟩ (Symbolic.encode .f32 (OnlineSoftmax.average score value l.keys))]) ∧
      final.core.thread.status = .done := by
  let mid := intPC (intAssign s "%p" 1) 73
  have hguard : Scalar.run ctx oracle code 2 s = .ok (mid,[]) := by
    have hg := ge_branch_run (ctx := ctx) (oracle := oracle) (code := code) (s := s)
      (lhs := "%j") (rhs := "%n") (pred := "%p") (target := 73) (x := l.keys) (y := l.keys)
      hi.running (by rw [hi.pc]; rfl) (by rw [hi.pc]; rfl) hi.index hi.keyCount l.keys32 l.keys32
    simpa only [le_refl,ite_true] using hg
  have hframe : RegisterFrame ["%p"] s mid := register_frame_trans
    (intAssign_register_frame hi.banks "%p" 1 (by decide)) (intPC_register_frame (intAssign_banks _ _ _) 73)
  have hregs := hi.online hkeys.ne'
  have hmidRegs : ScalarAttentionUpdate.Registers mid (OnlineSoftmax.run score value l.keys) :=
    ⟨((hframe "%max" (by decide)).2).trans hregs.1,
      ((hframe "%l" (by decide)).2).trans hregs.2.1,((hframe "%u" (by decide)).2).trans hregs.2.2⟩
  obtain ⟨final,htail,hdone⟩ := ScalarAttentionUpdate.normalize_store ctx oracle mid
    (OnlineSoftmax.run score value l.keys) score value l.keys l.output
    (by simpa [mid,intPC,intAssign,finishInteger,assign,Ptx.advance] using hi.running) rfl hmidRegs
    (OnlineSoftmax.run_inv score value l.keys) hkeys
    (((hframe "%op" (by decide)).1).trans hi.output) l.output64
  refine ⟨final,?_,hdone⟩
  rw [show 5 = 2+3 by decide,Scalar.run_add,hguard]
  simp only [Except.bind,htail,List.nil_append]

def suffixSteps (dim start : Nat) : Nat → Nat
  | 0 => 5
  | n+1 => iterationSteps dim start+suffixSteps dim (start+1) n

def suffixReads (l : Layout) (q key value : Attention.Matrix) (row col start : Nat) : Nat → List Scalar.Kind
  | 0 => []
  | n+1 => if h : start < l.keys then
      iterationReads l q key value row col start h ++ suffixReads l q key value row col (start+1) n
    else []

theorem suffixSteps_nonzero_start (dim start remaining : Nat) (hs : 0 < start) :
    suffixSteps dim start remaining = remaining*(9*dim+26)+5 := by
  induction remaining generalizing start with
  | zero => simp [suffixSteps]
  | succ n ih =>
    rw [suffixSteps,ih (start+1) (by omega)]
    simp only [iterationSteps,show start ≠ 0 from hs.ne',ite_false,Nat.succ_mul]
    omega

theorem suffixSteps_from_zero (dim count : Nat) (hn : 0 < count) :
    suffixSteps dim 0 count = count*(9*dim+26)-2 := by
  cases count with
  | zero => omega
  | succ n =>
    rw [suffixSteps,suffixSteps_nonzero_start dim 1 n (by decide)]
    simp only [iterationSteps,ite_true,Nat.succ_mul]
    omega

/-- Constructive completion of the actual nested outer loop through store/ret.
The count follows remaining iterations, not a chosen cutoff. Reply hypotheses
still describe a local execution; global memory correspondence remains separate. -/
theorem complete_suffix (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (q key value : Attention.Matrix) (row col : Nat) (scale : ℝ) (hkeys : 0 < l.keys)
    (hq : ∀ j k, j < l.keys → k < l.dim → oracle (queryIndex l j+2*k) = .real .f32 (q row k))
    (hk : ∀ j k, j < l.keys → k < l.dim → oracle (queryIndex l j+2*k+1) = .real .f32 (key j k))
    (hv : ∀ j, j < l.keys → oracle (queryIndex l j+2*l.dim) = .real .f32 (value j col))
    (remaining : Nat) :
    ∀ {start s}, l.keys = start+remaining →
      Inv l (scores l q key scale row) (fun item => value item col) scale start s →
      ∃ final, Scalar.run ctx oracle code (suffixSteps l.dim start remaining) s = .ok
        (final,suffixReads l q key value row col start remaining ++
          [.write ⟨.global,l.output⟩ (Symbolic.encode .f32
            (OnlineSoftmax.average (scores l q key scale row) (fun item => value item col) l.keys))]) ∧
        final.core.thread.status = .done := by
  induction remaining with
  | zero =>
    intro start s he hi
    have hs : start = l.keys := by omega
    subst start
    simpa only [suffixSteps,suffixReads,List.nil_append] using
      finish l ctx oracle (scores l q key scale row) (fun item => value item col) scale hkeys hi
  | succ n ih =>
    intro start s he hi
    have hj : start < l.keys := by omega
    obtain ⟨mid,hr,hm,_⟩ := iteration l ctx oracle q key value row col scale hi hj
      (hq start · hj ·) (hk start · hj ·) (hv start hj)
    obtain ⟨final,ht,hf⟩ := ih (by omega : l.keys = (start+1)+n) hm
    refine ⟨final,?_,hf⟩
    rw [suffixSteps,Scalar.run_add,hr]
    simp only [Except.bind,ht,suffixReads,dite_eq_left hj,List.append_assoc]

theorem complete_from_loop_entry (l : Layout) (ctx : Scalar.Context) (oracle : Scalar.Oracle)
    (q key value : Attention.Matrix) (row col : Nat) (scale : ℝ) (hkeys : 0 < l.keys)
    (hq : ∀ j k, j < l.keys → k < l.dim → oracle (queryIndex l j+2*k) = .real .f32 (q row k))
    (hk : ∀ j k, j < l.keys → k < l.dim → oracle (queryIndex l j+2*k+1) = .real .f32 (key j k))
    (hv : ∀ j, j < l.keys → oracle (queryIndex l j+2*l.dim) = .real .f32 (value j col))
    {s : Scalar.State} (hi : Inv l (scores l q key scale row) (fun item => value item col) scale 0 s) :
    ∃ final, Scalar.run ctx oracle code (l.keys*(9*l.dim+26)-2) s = .ok
      (final,suffixReads l q key value row col 0 l.keys ++
        [.write ⟨.global,l.output⟩ (Symbolic.encode .f32
          (Attention.output q key value (Real.log 2*scale) row col l.keys l.dim))]) ∧
      final.core.thread.status = .done := by
  have h := complete_suffix l ctx oracle q key value row col scale hkeys hq hk hv l.keys (by omega) hi
  have hb : OnlineSoftmax.average (scores l q key scale row) (fun item => value item col) l.keys =
      Attention.output q key value (Real.log 2*scale) row col l.keys l.dim :=
    OnlineSoftmax.attention_bridge q key value scale row col l.keys l.dim
  simpa only [suffixSteps_from_zero l.dim l.keys hkeys,hb] using h

end
end Ptx.ScalarAttentionOuter
