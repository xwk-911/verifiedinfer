import Ptx.Rules.Memory
import Iris.Algebra.Lib.DFracAgree
import Mathlib.Tactic.Linarith

/-! Fractional read/full write permissions and their operational race-safety rule.
The ledger is fixed for one synchronization epoch. Its realization by an Iris
global state, transfer at barriers, and asynchronous loans are separate obligations.
In particular this module does not silently assume that tokens imply history ownership.
-/
namespace Ptx.Permissions

/-- Pairwise compatibility suffices for the no-read/write-conflict theorem below.
This is not claimed to be the complete fractional heap CMRA validity predicate. -/
structure Ledger where
  share : Nat → Space → Nat → Rat
  nonnegative : ∀ tid space addr, 0 ≤ share tid space addr
  compatible : ∀ t u space addr, t ≠ u → share t space addr + share u space addr ≤ 1

/-- A concrete family of valid ledgers for arbitrary address-to-thread ownership.
This also supplies nonvacuous permission preconditions for kernel contracts. -/
def ownerLedger (owner : Space → Nat → Nat) : Ledger where
  share tid space addr := if owner space addr = tid then 1 else 0
  nonnegative := by intro tid space addr; split <;> simp
  compatible := by
    intro t u space addr hne
    by_cases ht : owner space addr = t
    · have hu : owner space addr ≠ u := by intro hu; exact hne (ht.symm.trans hu)
      simp [ht,hne]
    · by_cases hu : owner space addr = u
      · simp [hu, Ne.symm hne]
      · simp [ht,hu]

theorem ownerLedger_full (owner : Space → Nat → Nat) (space : Space) (addr : Nat) :
    (ownerLedger owner).share (owner space addr) space addr = 1 := by simp [ownerLedger]

def Granted (p : Ledger) (a : Access) : Prop :=
  if a.write then p.share a.thread a.space a.address = 1
  else 0 < p.share a.thread a.space a.address

def HistoryOwned (p : Ledger) (m : Machine) : Prop :=
  ∀ a ∈ m.history, a.epoch = m.epoch → Granted p a

theorem granted_positive {p a} (hg : Granted p a) :
    0 < p.share a.thread a.space a.address := by
  cases h : a.write <;> simp [Granted, h] at hg
  · exact hg
  · rw [hg]; decide

/-- A positive read share or full write share is compatible with all accesses
recorded in the current epoch under the same ledger. -/
theorem permission_no_conflict {p m a} (hh : HistoryOwned p m)
    (hg : Granted p a) (he : a.epoch = m.epoch) :
    m.history.find? (conflict a) = none := by
  apply List.find?_eq_none.mpr
  intro b hb hc
  simp only [conflict, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨⟨hspace,haddr⟩,htid⟩,hepoch⟩,hwrite⟩ := hc
  have hgb := hh b hb (hepoch.symm.trans he)
  have hposA := granted_positive hg
  have hposB : 0 < p.share b.thread a.space a.address := by
    simpa [hspace,haddr] using granted_positive hgb
  have hsum := p.compatible a.thread b.thread a.space a.address htid
  rcases hwrite with ha | hb
  · have hfull : p.share a.thread a.space a.address = 1 := by simpa [Granted, ha] using hg
    linarith
  · have hfull : p.share b.thread a.space a.address = 1 := by
      simpa [Granted, hb, hspace, haddr] using hgb
    linarith

theorem permission_accessOK {p m a} (hh : HistoryOwned p m) (hg : Granted p a)
    (he : a.epoch = m.epoch) (ha : a.address % 4 = 0)
    (hb : a.address / 4 < (memory m a.space).length) : AccessOK m a :=
  ⟨ha,hb,permission_no_conflict hh hg he⟩

theorem historyOwned_record {p m a} (hh : HistoryOwned p m) (hg : Granted p a) :
    HistoryOwned p { m with history := a :: m.history } := by
  intro b hb he
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hg
  · exact hh b hb he

def HistoryPast (m : Machine) : Prop := ∀ a ∈ m.history, a.epoch ≤ m.epoch

theorem historyPast_record {m a} (hh : HistoryPast m) (he : a.epoch = m.epoch) :
    HistoryPast { m with history := a :: m.history } := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact Nat.le_of_eq he
  · exact hh b hb

/-- After the actual full-CTA rendezvous, every old access is in a strictly earlier
epoch. Any new compatible ledger can therefore describe the next phase. This is
an operational ordering rule; a BI resource redistribution still needs its own
joint interpretation proof. No synchronization is inserted into the kernel. -/
theorem barrier_regrant {m m'} (hh : HistoryPast m) (hs : release m = .ok m')
    (newLedger : Ledger) : HistoryPast m' ∧ HistoryOwned newLedger m' := by
  unfold release at hs
  cases ht : m.threads.head? with
  | none => simp [ht, bind, Except.bind] at hs
  | some t =>
    cases hstatus : t.status with
    | running => simp [ht, hstatus, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs
    | done => simp [ht, hstatus, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs
    | waiting id =>
      by_cases hall : m.threads.all (fun t => t.status == .waiting id) = true
      · simp [ht,hstatus,hall,bind,Except.bind,pure,Except.pure] at hs
        subst m'
        constructor
        · intro a ha
          have := hh a ha
          change a.epoch ≤ m.epoch + 1
          omega
        · intro a ha he
          have hp := hh a ha
          change a.epoch = m.epoch + 1 at he
          omega
      · simp [ht,hstatus,hall,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hs

/-- An operational read rule: permissions discharge the interpreter's conflict
check, while bounds/initialization remain explicit physical-memory obligations. -/
theorem load_rule {p code tid m t space dst addr value address}
    (ht : m.threads[tid]? = some t) (hr : t.status = .running)
    (hpc : code[t.pc]? = some (.load space dst address))
    (heval : evalAddr tid t address = .ok addr)
    (hh : HistoryOwned p m) (hread : 0 < p.share tid space addr)
    (ha : addr % 4 = 0) (hb : addr / 4 < (memory m space).length)
    (hv : (memory m space)[addr/4]? = some (some value)) :
    ∃ m', threadStep code tid m = .ok m' ∧ HistoryOwned p m' := by
  let a : Access := ⟨space,addr,tid,false,m.epoch⟩
  have hg : Granted p a := hread
  have hstep := threadStep_load ht hr hpc heval (permission_accessOK hh hg rfl ha hb) hv
  refine ⟨_, hstep, ?_⟩
  exact historyOwned_record hh hg

theorem store_rule {p code tid m t space addr value address operand}
    (ht : m.threads[tid]? = some t) (hr : t.status = .running)
    (hpc : code[t.pc]? = some (.store space address operand))
    (heval : evalAddr tid t address = .ok addr) (hv : eval tid t operand = .ok value)
    (hh : HistoryOwned p m) (hwrite : p.share tid space addr = 1)
    (ha : addr % 4 = 0) (hb : addr / 4 < (memory m space).length) :
    ∃ m', threadStep code tid m = .ok m' ∧ HistoryOwned p m' := by
  let a : Access := ⟨space,addr,tid,true,m.epoch⟩
  have hg : Granted p a := hwrite
  have hstep := threadStep_store ht hr hpc heval hv (permission_accessOK hh hg rfl ha hb)
  refine ⟨_, hstep, ?_⟩
  cases space <;> exact historyOwned_record hh hg

/-! Camera-level resource laws, using Iris-Lean's existing fraction/agreement CMRA.
These are reusable algebra laws, not a new research contribution or adequacy proof. -/
open Iris Iris.ORA Iris.DFracAgree
abbrev Cell := DFracAgreeR (DiscreteO Nat)
def cell (q : Qp) (value : Nat) : Cell := mk (.own q) ⟨value⟩

theorem share_at_most_one (p : Ledger) (tid : Nat) (space : Space) (addr : Nat) :
    p.share tid space addr ≤ 1 := by
  have hsum := p.compatible tid (tid+1) space addr (by omega)
  have hnonneg := p.nonnegative (tid+1) space addr
  linarith

/-- The ledger's actual positive read amount yields a valid Iris cell fragment.
This connects the single-cell arithmetic, while global realization remains open. -/
theorem ledger_cell_valid (p : Ledger) (tid : Nat) (space : Space) (addr value : Nat)
    (hread : 0 < p.share tid space addr) :
    ✓ (cell ⟨p.share tid space addr,hread⟩ value) := by
  apply DFracAgree.mk_valid.mpr
  change p.share tid space addr ≤ 1
  exact share_at_most_one p tid space addr

theorem read_split (q : Qp) (v : Nat) : cell q v = cell q.half v • cell q.half v := by
  unfold cell
  rw [← mk_op]
  congr 1
  change DFrac.own q = DFrac.own (q.half + q.half)
  rw [Qp.half_add_half]

theorem read_agree {q r : Qp} {v w : Nat} (h : ✓ (cell q v • cell r w)) : v = w := by
  have ha := (DFracAgree.op_valid.mp h).2
  exact congrArg DiscreteO.car ha

theorem full_write_exclusive (q : Qp) (v w : Nat) : ¬ ✓ (cell 1 v • cell q w) := by
  unfold cell
  exact not_valid_excl_op_left

end Ptx.Permissions
