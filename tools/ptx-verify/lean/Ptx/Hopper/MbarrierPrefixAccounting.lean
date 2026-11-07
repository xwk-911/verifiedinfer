import Ptx.Hopper.MbarrierAccounting

/-! Counted prefix equations for a single actual initialization. The operational
accounting supports reinitialization; replacing its reset counters with global
prefix totals requires the separately established one-initialization inventory.
No canonical transfer or wait order is required. -/
namespace Ptx.Hopper.Mbarrier
open Ptx.ISA

def isInitialization : BarrierOp → Bool
  | .init _ => true
  | _ => false
def arrivalUnit : BarrierOp → Nat
  | .arriveExpectTx _ => 1
  | _ => 0
def addedUnit : BarrierOp → Nat
  | .arriveExpectTx n => n
  | _ => 0
def completedUnit : BarrierOp → Nat
  | .completeTx n => n
  | _ => 0
def arrivalCount (ops : List BarrierOp) : Nat := (ops.map arrivalUnit).sum
def addedBytes (ops : List BarrierOp) : Nat := (ops.map addedUnit).sum
def completedBytes (ops : List BarrierOp) : Nat := (ops.map completedUnit).sum

theorem fold_accounting_without_initialization {ops : List BarrierOp} (a : Accounting)
    (hu : ∀ op ∈ ops, isInitialization op = false) :
    ops.foldl accountStep a = ⟨a.expected,a.arrivals+arrivalCount ops,a.added+addedBytes ops,a.completed+completedBytes ops⟩ := by
  induction ops generalizing a with
  | nil => simp [arrivalCount,addedBytes,completedBytes]
  | cons op rest ih =>
    have hhead := hu op (by simp)
    have htail : ∀ x ∈ rest, isInitialization x = false := fun x hx => hu x (by simp [hx])
    rw [List.foldl_cons,ih _ htail]
    cases op <;> simp_all [isInitialization,accountStep,arrivalCount,addedBytes,completedBytes,
      arrivalUnit,addedUnit,completedUnit,Nat.add_assoc]

theorem single_initialization_shape {ops last}
    (hi : (ops.filter isInitialization).length = 1)
    (hu : ∀ op ∈ ops, UnitInitialization op) (hr : run none ops = some last) :
    ∃ rest, ops = .init 1 :: rest ∧ ∀ op ∈ rest, isInitialization op = false := by
  cases ops with
  | nil => simp at hi
  | cons op rest =>
    cases op <;> try (simp [run,step] at hr)
    case init n =>
      have hn : n = 1 := hu (.init n) (by simp)
      subst n
      refine ⟨rest,rfl,?_⟩
      have hz : (rest.filter isInitialization).length = 0 := by
        simp only [List.filter_cons,isInitialization,Bool.true_eq,ite_true,List.length_cons] at hi
        omega
      have he : rest.filter isInitialization = [] := by simpa using hz
      intro op hop
      simpa using List.filter_eq_nil_iff.mp he op hop

theorem single_initialization_prefix_counts {ops last}
    (hi : (ops.filter isInitialization).length = 1)
    (hu : ∀ op ∈ ops, UnitInitialization op) (hr : run none ops = some last) (cut : Nat) :
    (account (ops.take cut)).arrivals = arrivalCount (ops.take cut) ∧
      (account (ops.take cut)).added = addedBytes (ops.take cut) ∧
      (account (ops.take cut)).completed = completedBytes (ops.take cut) := by
  obtain ⟨rest,rfl,hrest⟩ := single_initialization_shape hi hu hr
  cases cut with
  | zero => simp [account,arrivalCount,addedBytes,completedBytes]
  | succ cut =>
    have htake : ∀ op ∈ rest.take cut, isInitialization op = false := fun op hop => hrest op (List.mem_of_mem_take hop)
    simp only [List.take_succ_cons,account,List.foldl_cons,accountStep]
    rw [fold_accounting_without_initialization _ htake]
    simp [arrivalCount,addedBytes,completedBytes,arrivalUnit,addedUnit,completedUnit]

theorem single_initialization_prefix_balance {ops last state}
    (hi : (ops.filter isInitialization).length = 1)
    (hu : ∀ op ∈ ops, UnitInitialization op) (hr : run none ops = some last) (cut : Nat)
    (hp : run none (ops.take cut) = some (some state)) :
    state.expected = 1 ∧ state.pending ≤ 1 ∧
      state.phase+1 = arrivalCount (ops.take cut)+state.pending ∧
      state.tx = (addedBytes (ops.take cut) : Int)-(completedBytes (ops.take cut) : Int) := by
  have hunit : ∀ op ∈ ops.take cut, UnitInitialization op := fun op hop => hu op (List.mem_of_mem_take hop)
  obtain ⟨he,hpending,hphase,htx⟩ := run_unit_accounting hunit hp
  obtain ⟨ha,hb,hc⟩ := single_initialization_prefix_counts hi hu hr cut
  rw [ha] at hphase
  rw [hb,hc] at htx
  exact ⟨he,hpending,hphase,htx⟩

theorem single_initialization_live_prefix_lifetime {ops last state}
    (hi : (ops.filter isInitialization).length = 1)
    (hu : ∀ op ∈ ops, UnitInitialization op) (hr : run none ops = some last) (cut : Nat)
    (hp : run none (ops.take cut) = some (some state)) :
    ((ops.take cut).filter isInitialization).length = 1 := by
  obtain ⟨rest,rfl,hrest⟩ := single_initialization_shape hi hu hr
  cases cut with
  | zero => simp [run] at hp
  | succ cut =>
    have hn : (rest.take cut).filter isInitialization = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro op hop
      simp only [hrest op (List.mem_of_mem_take hop),Bool.false_eq_true,not_false_eq_true]
    simp only [List.take_succ_cons,List.filter_cons,isInitialization,Bool.true_eq,ite_true,List.length_cons]
    rw [hn]
    rfl

def FixedArrival (bytes : Nat) : BarrierOp → Prop
  | .arriveExpectTx n => n = bytes
  | _ => True

theorem fixed_arrival_added_bytes {ops : List BarrierOp} (bytes : Nat)
    (hf : ∀ op ∈ ops, FixedArrival bytes op) : addedBytes ops = bytes*arrivalCount ops := by
  induction ops with
  | nil => simp [addedBytes,arrivalCount]
  | cons op rest ih =>
    have hhead := hf op (by simp)
    have htail := ih (fun x hx => hf x (by simp [hx]))
    cases op <;> simp_all [FixedArrival,addedBytes,arrivalCount,addedUnit,arrivalUnit,Nat.mul_add]

end Ptx.Hopper.Mbarrier
