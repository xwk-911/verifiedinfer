import Ptx.Rules.Local

/-! Operational load/store contracts. These are quantified over arbitrary machines,
addresses and values, and prove successful execution, not just postconditions of
an assumed successful step. Ownership rules may discharge AccessOK separately. -/
namespace Ptx

structure AccessOK (m : Machine) (a : Access) : Prop where
  aligned : a.address % 4 = 0
  bounds : a.address / 4 < (memory m a.space).length
  ordered : m.history.find? (conflict a) = none

theorem checkedAccess_ok {m a} (h : AccessOK m a) :
    checkedAccess m a = .ok { m with history := a :: m.history } := by
  simp [checkedAccess, h.aligned, Nat.not_le_of_lt h.bounds, h.ordered]

theorem threadStep_load {code tid m t space dst addr value address}
    (ht : m.threads[tid]? = some t) (hr : t.status = .running)
    (hpc : code[t.pc]? = some (.load space dst address))
    (heval : evalAddr tid t address = .ok addr)
    (ha : AccessOK m ⟨space,addr,tid,false,m.epoch⟩)
    (hv : (memory m space)[addr/4]? = some (some value)) :
    threadStep code tid m = .ok (updateThread { m with history :=
      ⟨space,addr,tid,false,m.epoch⟩ :: m.history } tid (assign t dst (wrap 32 value))) := by
  cases space <;> simp only [memory] at hv <;>
    simp [threadStep, ht, hr, hpc, heval, checkedAccess_ok ha, memory, hv,
      bind, Except.bind, pure, Except.pure]

theorem threadStep_store {code tid m t space addr value address operand}
    (ht : m.threads[tid]? = some t) (hr : t.status = .running)
    (hpc : code[t.pc]? = some (.store space address operand))
    (heval : evalAddr tid t address = .ok addr) (hv : eval tid t operand = .ok value)
    (ha : AccessOK m ⟨space,addr,tid,true,m.epoch⟩) :
    threadStep code tid m = .ok (updateThread
      (setMemory { m with history := ⟨space,addr,tid,true,m.epoch⟩ :: m.history }
        space ((memory m space).set (addr/4) (some (wrap 32 value)))) tid (advance t)) := by
  cases space <;> simp [threadStep, ht, hr, hpc, heval, hv, checkedAccess_ok ha,
    memory, bind, Except.bind, pure, Except.pure]

@[simp] theorem memory_updateThread (m : Machine) (tid : Nat) (t : Thread) (space : Space) :
    memory (updateThread m tid t) space = memory m space := by cases space <;> rfl
@[simp] theorem memory_history (m : Machine) (history : List Access) (space : Space) :
    memory { m with history := history } space = memory m space := by cases space <;> rfl
@[simp] theorem memory_setMemory_same (m : Machine) (space : Space) (xs : List (Option Nat)) :
    memory (setMemory m space xs) space = xs := by cases space <;> rfl
theorem memory_setMemory_other {m space other xs} (hne : other ≠ space) :
    memory (setMemory m space xs) other = memory m other := by
  cases space <;> cases other <;> simp_all [memory, setMemory]

/-- The frame property of an aligned store: all other cells in both spaces retain
their exact value. Arithmetic on byte offsets is justified, not assumed. -/
theorem store_frame {m : Machine} {space other : Space} {addr addr' value : Nat}
    (halign : addr % 4 = 0) (halign' : addr' % 4 = 0)
    (hdiff : other ≠ space ∨ addr' ≠ addr) :
    (memory (setMemory m space ((memory m space).set (addr/4) (some value))) other)[addr'/4]? =
      (memory m other)[addr'/4]? := by
  by_cases hspace : other = space
  · subst other
    have haddr : addr' ≠ addr := hdiff.resolve_left (by simp)
    have hi : addr / 4 ≠ addr' / 4 := by omega
    simp [List.getElem?_set_ne hi]
  · rw [memory_setMemory_other hspace]

theorem store_value {m : Machine} {space : Space} {addr value : Nat}
    (hb : addr / 4 < (memory m space).length) :
    (memory (setMemory m space ((memory m space).set (addr/4) (some value))) space)[addr/4]? =
      some (some value) := by simp [List.getElem?_set_self hb]

end Ptx
