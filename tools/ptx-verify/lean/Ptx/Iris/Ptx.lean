import Ptx.Iris.Execution
import Ptx.Kernels.Copy
import Ptx.Kernels.SharedSwap

/-! Iris rules for the SAME PTX interpreter used by the kernel contracts.
Physical ownership is whole-machine OwnP; read/write ledgers and history are
explicit pure state invariants. No per-cell Iris token interpretation is asserted.
-/
namespace Ptx.IrisPtx
open Iris Iris.BI Iris.ProgramLogic

def transition (code : List Instr) (a : Action) (m : Machine) := Ptx.step code a m
abbrev Expr (code : List Instr) := IrisExecution.Expr (transition code)
abbrev invoke (code : List Instr) (a : Action) : Expr code := IrisExecution.Expr.invoke a
abbrev script (code : List Instr) (actions : List Action) : Expr code := IrisExecution.Expr.script actions
noncomputable abbrev GF := IrisExecution.GF Machine
local bi (IProp GF)

theorem invoke_wp [OwnPGS Machine GF] {code m a result} (hs : step code a m = result) :
    ownP (GF := GF) m ⊢ WP (invoke code a)
      {{ v, ⌜v = result⌝ ∗ ownP (IrisExecution.after m v) }} :=
  IrisExecution.invoke_wp hs

theorem invoke_frame [OwnPGS Machine GF] {code m a result} (hs : step code a m = result)
    (R : IProp GF) :
    ownP (GF := GF) m ∗ R ⊢ WP (invoke code a)
      {{ v, R ∗ ⌜v = result⌝ ∗ ownP (IrisExecution.after m v) }} :=
  IrisExecution.invoke_frame hs R

theorem ensures_wp [OwnPGS Machine GF] {code m a} (Q : Machine → Prop)
    (hr : ∃ m', step code a m = .ok m' ∧ Q m') :
    ownP (GF := GF) m ⊢ WP (invoke code a)
      {{ v, ∃ m', ⌜v = .ok m' ∧ Q m'⌝ ∗ ownP m' }} := by
  obtain ⟨m',hs,hq⟩ := hr
  refine (invoke_wp hs).trans (wp_mono ?_)
  intro v
  iintro ⟨%hv, Hnext⟩
  subst v
  simp only [IrisExecution.after]
  iexists m'
  isplit
  · ipureintro; exact ⟨rfl,hq⟩
  · iexact Hnext

/-- Fractions discharge the actual conflict check, not a replacement load. -/
theorem load_wp [OwnPGS Machine GF] {p code tid m t space dst addr value address}
    (ht : m.threads[tid]? = some t) (hr : t.status = .running)
    (hpc : code[t.pc]? = some (.load space dst address))
    (heval : evalAddr tid t address = .ok addr)
    (hh : Permissions.HistoryOwned p m) (hread : 0 < p.share tid space addr)
    (ha : addr % 4 = 0) (hb : addr / 4 < (memory m space).length)
    (hv : (memory m space)[addr/4]? = some (some value)) :
    ownP (GF := GF) m ⊢ WP (invoke code (.thread tid))
      {{ v, ∃ m', ⌜v = .ok m' ∧ Permissions.HistoryOwned p m'⌝ ∗ ownP m' }} :=
  ensures_wp _ (Permissions.load_rule ht hr hpc heval hh hread ha hb hv)

theorem store_wp [OwnPGS Machine GF] {p code tid m t space addr value address operand}
    (ht : m.threads[tid]? = some t) (hr : t.status = .running)
    (hpc : code[t.pc]? = some (.store space address operand))
    (heval : evalAddr tid t address = .ok addr) (hv : eval tid t operand = .ok value)
    (hh : Permissions.HistoryOwned p m) (hwrite : p.share tid space addr = 1)
    (ha : addr % 4 = 0) (hb : addr / 4 < (memory m space).length) :
    ownP (GF := GF) m ⊢ WP (invoke code (.thread tid))
      {{ v, ∃ m', ⌜v = .ok m' ∧ Permissions.HistoryOwned p m'⌝ ∗ ownP m' }} :=
  ensures_wp _ (Permissions.store_rule ht hr hpc heval hv hh hwrite ha hb)

/-- Operational epoch regrant under OwnP, not a per-cell token redistribution. -/
theorem barrier_wp [OwnPGS Machine GF] {code m m'} (hp : Permissions.HistoryPast m)
    (hs : release m = .ok m') (newLedger : Permissions.Ledger) :
    ownP (GF := GF) m ⊢ WP (invoke code .release)
      {{ v, ∃ m', ⌜v = .ok m' ∧
        Permissions.HistoryPast m' ∧ Permissions.HistoryOwned newLedger m'⌝ ∗ ownP m' }} :=
  ensures_wp _ ⟨m',hs,Permissions.barrier_regrant hp hs newLedger⟩

theorem run_eq (code : List Instr) (actions : List Action) (m : Machine) :
    IrisExecution.run (transition code) actions m = run code actions m := by
  induction actions generalizing m with
  | nil => rfl
  | cons a actions ih =>
    cases h : step code a m <;>
      simp [IrisExecution.run,run,transition,h,Except.bind,ih]

theorem script_wp [OwnPGS Machine GF] {code actions m m'} (hs : run code actions m = .ok m') :
    ownP (GF := GF) m ⊢ WP (script code actions) {{ v, ⌜v = .ok m'⌝ ∗ ownP m' }} :=
  IrisExecution.script_wp ((run_eq code actions m).trans hs)

/-- Connects all-input/all-finite-schedule kernel contracts to this Iris language.
The successful trace premise is explicit; universal absence of PTX faults is the
separate kernel Safe theorem, not inferred from NotStuck of error-valued scripts. -/
theorem contract_wp [OwnPGS Machine GF] {code P Q actions m m'}
    (hc : Triple code P Q) (hp : P m) (hs : run code actions m = .ok m')
    (hd : m'.threads.all (fun t => t.status == .done) = true) :
    ownP (GF := GF) m ⊢ WP (script code actions)
      {{ v, ⌜v = .ok m' ∧ Q m'⌝ ∗ ownP m' }} := by
  have hq := hc m m' hp (run_sound hs) hd
  refine (script_wp hs).trans (wp_mono ?_)
  intro v
  iintro ⟨%hv, Hnext⟩
  isplit
  · ipureintro; exact ⟨hv,hq⟩
  · iexact Hnext

theorem contract_adequate {code P Q actions m m'} (hc : Triple code P Q) (hp : P m)
    (hs : run code actions m = .ok m')
    (hd : m'.threads.all (fun t => t.status == .done) = true) :
    adequate .NotStuck (script code actions) m (fun v _ => v = .ok m' ∧ Q m') := by
  apply ownP_adequacy (GF := GF) .NotStuck (script code actions) m (fun v => v = .ok m' ∧ Q m')
  intro _
  refine (contract_wp hc hp hs hd).trans (wp_mono ?_)
  intro v
  iintro ⟨Hv, _⟩
  iexact Hv

theorem copy_adequate {c actions m m'} (hp : CopyContract.Pre c m)
    (hs : run CopyContract.code actions m = .ok m')
    (hd : m'.threads.all (fun t => t.status == .done) = true) :
    adequate .NotStuck (script CopyContract.code actions) m
      (fun v _ => v = .ok m' ∧ CopyContract.Post c m') :=
  contract_adequate (CopyContract.correct c) hp hs hd

theorem shared_adequate {c actions m m'} (hp : SharedContract.Pre c m)
    (hs : run SharedContract.code actions m = .ok m')
    (hd : m'.threads.all (fun t => t.status == .done) = true) :
    adequate .NotStuck (script SharedContract.code actions) m
      (fun v _ => v = .ok m' ∧ SharedContract.Post c m') :=
  contract_adequate (SharedContract.correct c) hp hs hd

theorem reject_not_ok_adequate {code actions m error} (hs : run code actions m = .error error) :
    ¬ adequate .NotStuck (script code actions) m (fun v _ => ∃ m', v = .ok m') :=
  IrisExecution.script_reject_not_ok_adequate ((run_eq code actions m).trans hs)

end Ptx.IrisPtx
