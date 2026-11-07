import Ptx.ISA.Typing
import Ptx.Rules.Local
import Ptx.Event.Thread

/-! Connections to the SAME fixed interpreters, and bounded-value preservation
for successful local steps. Type correctness does not initialize registers or
memory, discharge access safety, prove termination, or prove kernel contracts.
-/
namespace Ptx.ISA

def RegistersTyped (declarations : RegisterDeclarations) (bindings : Bindings) : Prop :=
  ∀ name ty value, declarationLookup name declarations = some ty → lookup name bindings = some value → value < 2^ty.bits

theorem registers_empty (declarations : RegisterDeclarations) : RegistersTyped declarations [] := by
  intro name ty value _ h
  simp [lookup] at h

theorem registers_put {declarations bindings width name value}
    (hf : RegisterFits declarations width name) (hv : value < 2^width) (hi : RegistersTyped declarations bindings) :
    RegistersTyped declarations (put name value bindings) := by
  intro other ty observed hdecl hread
  by_cases hn : other = name
  · subst other
    have he : value = observed := by simpa only [lookup_put_same,Option.some.injEq] using hread
    have hw : ty.bits = width := register_fits_bits hf hdecl
    rw [← he,hw]
    exact hv
  · apply hi other ty observed hdecl
    simpa only [lookup_put_other hn] using hread

theorem wrap_bound (width value : Nat) : wrap width value < 2^width :=
  Nat.mod_lt value (Nat.two_pow_pos width)

theorem local_preserves_types {declarations parameters length params tid t next instruction}
    (ht : InstructionTyped declarations parameters length instruction) (hi : RegistersTyped declarations t.regs)
    (hs : localStep params tid t instruction = .ok next) : RegistersTyped declarations next.regs := by
  cases instruction with
  | mov width dst src =>
    simp only [localStep,bind,Except.bind,pure,Except.pure] at hs
    repeat' first | split at hs | (cases hs)
    exact registers_put ht.2.1 (wrap_bound _ _) hi
  | param width dst name =>
    simp only [localStep,bind,Except.bind,pure,Except.pure] at hs
    repeat' first | split at hs | (cases hs)
    exact registers_put ht.2.1 (wrap_bound _ _) hi
  | bin op input output dst a b =>
    simp only [localStep,bind,Except.bind,pure,Except.pure] at hs
    repeat' first | split at hs | (cases hs)
    all_goals exact registers_put ht.2.1 (wrap_bound _ _) hi
  | setp cmp dst a b =>
    simp only [localStep,bind,Except.bind,pure,Except.pure] at hs
    repeat' first | split at hs | (cases hs)
    all_goals exact registers_put ht.1 (by decide) hi
  | branch pred positive target =>
    simp only [localStep,bind,Except.bind,pure,Except.pure] at hs
    repeat' first | split at hs | (cases hs)
    all_goals exact hi
  | jump target => cases hs; exact hi
  | barrier bid => cases hs; exact hi
  | ret => cases hs; exact hi
  | load space dst address => cases hs
  | store space address value => cases hs

theorem event_step_preserves_types (program : CheckedProgram) {ctx oracle initial next events}
    (hi : RegistersTyped program.registers initial.thread.regs)
    (hs : Event.step ctx oracle program.code initial = .ok (next,events)) :
    RegistersTyped program.registers next.thread.regs := by
  by_cases hr : initial.thread.status = .running
  · cases hc : program.code[initial.thread.pc]? with
    | none => simp [Event.step,hr,hc,bind,Except.bind] at hs
    | some instruction =>
      have ht := program.instruction_typed (List.mem_of_getElem? hc)
      cases instruction <;> simp [Event.step,hr,hc,bind,Except.bind,pure,Except.pure] at hs
      all_goals
        repeat' first | split at hs | (cases hs)
        all_goals first
          | exact hi
          | (subst next; exact hi)
          | exact registers_put ht.1 (wrap_bound _ _) hi
          | exact local_preserves_types ht hi (by assumption)
  · simp [Event.step,hr,bind,Except.bind] at hs

theorem event_runs_preserve_types (program : CheckedProgram) {ctx oracle initial next events}
    (hs : Event.Runs ctx oracle program.code initial events next)
    (hi : RegistersTyped program.registers initial.thread.regs) :
    RegistersTyped program.registers next.thread.regs := by
  induction hs with
  | nil => exact hi
  | cons hstep _ ih => exact ih (event_step_preserves_types program hi hstep)

theorem event_run_preserves_types (program : CheckedProgram) {ctx oracle steps initial next events}
    (hs : Event.run ctx oracle program.code steps initial = .ok (next,events))
    (hi : RegistersTyped program.registers initial.thread.regs) :
    RegistersTyped program.registers next.thread.regs := event_runs_preserve_types program (Event.run_sound hs) hi

def CheckedProgram.run (program : CheckedProgram) (actions : List Action) (initial : Machine) : Except Fault Machine :=
  Ptx.run (program.instructions.map Subtype.val) actions initial

theorem CheckedProgram.run_erases (program : CheckedProgram) (actions : List Action) (initial : Machine) :
    program.run actions initial = Ptx.run program.code actions initial := by
  simp only [CheckedProgram.run,program.instructions_erase]

def CheckedProgram.eventRun (program : CheckedProgram) (ctx : Event.Context) (oracle : Event.Oracle)
    (steps : Nat) (initial : Event.State) : Except Fault (Event.State × List Event.Kind) :=
  Event.run ctx oracle (program.instructions.map Subtype.val) steps initial

theorem CheckedProgram.event_run_erases (program : CheckedProgram) (ctx : Event.Context) (oracle : Event.Oracle)
    (steps : Nat) (initial : Event.State) :
    program.eventRun ctx oracle steps initial = Event.run ctx oracle program.code steps initial := by
  simp only [CheckedProgram.eventRun,program.instructions_erase]

end Ptx.ISA
