import Ptx.Hopper.WgmmaRules
import Ptx.Generated.WgmmaProbe

/-! Local register/group tests and actual assembled-source execution. Replies
are checked for source protocol behavior only, not collective tensor arithmetic
or shared descriptor/memory validity. No GPU execution verdict is claimed. -/
namespace Ptx.WgmmaProtocolTests
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

def d : Ampere.Registers4 := ⟨"%d0","%d1","%d2","%d3"⟩
def ctx : Scalar.Context := {id := ⟨.zero,.zero⟩,params := [],block := ⟨128,1,1⟩}
def oracle : Wgmma.Oracle := {
  base := {
    ampere := {scalar := fun _ => .integer 0,bytes := fun _ => []}
    wait := fun _ => false
    descriptor := fun _ => ⟨0,16,1,16,16,1,1⟩
    tmaBytes := fun _ => List.replicate 16 (.bits (byte 0))
  }
  matrix := fun q _ => if q = 0 then 10 else 20
}
def seed : Wgmma.State := {base := {scalar := {
  core := {thread := {regs := [("%a",0),("%b",0)]}}
  floats := [("%d0",(.f32,1)),("%d1",(.f32,1)),("%d2",(.f32,1)),("%d3",(.f32,1))]
}}}
def fence : Hopper.Instr := .wgmma .fence
def mma : Hopper.Instr := .wgmma (.mma d "%a" "%b" (.imm 1))
def commit : Hopper.Instr := .wgmma .commit
def wait0 : Hopper.Instr := .wgmma (.wait 0)
def store : Hopper.Instr := .ampere (.scalar (.store .f32 .global ⟨.imm 8192,0⟩ (.reg "%d0")))
def zero : Scalar.F32Literal := ⟨0,by decide,by decide⟩
def overwrite : Hopper.Instr := .ampere (.scalar (.mov .f32 "%d0" (.literal zero)))
def result (code : List Hopper.Instr) (count : Nat) (o : Wgmma.Oracle := oracle) : Wgmma.State × List Wgmma.Event :=
  (Wgmma.run ctx o code count seed).toOption.getD ({},[])

theorem predicate_scale_typed : Wgmma.InstructionTyped
    (Generated.wgmma_probe.registerDeclarations++[("%p",.integer .pred)])
    (.mma d "%a" "%b" (.reg "%p")) := by decide
theorem integer_scale_register_not_typed : ¬Wgmma.InstructionTyped
    Generated.wgmma_probe.registerDeclarations (.mma d "%a" "%b" (.reg "%thread")) := by decide

theorem first_mma_needs_fence : Wgmma.run ctx oracle [mma] 1 seed = .error .needsFence := by rfl
theorem read_before_wait_rejected : Wgmma.run ctx oracle [fence,mma,store] 3 seed = .error (.pendingRegister "%d0") := by rfl
theorem write_before_wait_rejected : Wgmma.run ctx oracle [fence,mma,overwrite] 3 seed = .error (.pendingRegister "%d0") := by rfl
theorem commit_does_not_wait : Wgmma.run ctx oracle [fence,mma,commit,store] 4 seed = .error (.pendingRegister "%d0") := by rfl
theorem wait_does_not_commit : Wgmma.run ctx oracle [fence,mma,wait0,store] 4 seed = .error (.pendingRegister "%d0") := by rfl
theorem recent_group_stays_pending : Wgmma.run ctx oracle [fence,mma,commit,.wgmma (.wait 1),store] 5 seed = .error (.pendingRegister "%d0") := by rfl
theorem generic_access_needs_new_fence : Wgmma.run ctx oracle [fence,overwrite,mma] 3 seed = .error (.dirtyRegister "%d0") := by rfl
theorem fence_is_not_completion : Wgmma.run ctx oracle [fence,mma,fence,store] 4 seed = .error (.pendingRegister "%d0") := by rfl
theorem generic_read_requires_refence : Wgmma.run ctx oracle [fence,mma,commit,wait0,store,mma] 6 seed = .error (.dirtyRegister "%d0") := by rfl
theorem refence_allows_reuse : (Wgmma.run ctx oracle [fence,mma,commit,wait0,store,fence,mma,commit,wait0] 9 seed).toOption.isSome = true := by decide
theorem invalid_dynamic_wait_rejected : Wgmma.run ctx oracle [.wgmma (.wait 8)] 1 seed = .error (.waitCount 8) := by rfl
theorem scale_zero_does_not_read_uninitialized_accumulator :
    (Wgmma.run ctx oracle [fence,.wgmma (.mma d "%a" "%b" (.imm 0)),commit,wait0] 4
      {seed with base := {seed.base with scalar := {seed.base.scalar with floats := []}}}).toOption.isSome = true := by decide

theorem issue_keeps_visible_value : declarationLookup "%d0" (result [fence,mma] 2).1.base.scalar.floats = some (.f32,1) := by rfl
theorem issue_records_future_value : Wgmma.pendingValue (result [fence,mma] 2).1.ledger "%d0" = some 10 := by rfl
theorem committed_wait_publishes_value : declarationLookup "%d0" (result [fence,mma,commit,wait0] 4).1.base.scalar.floats = some (.f32,10) := by rfl
theorem chain_reads_prior_async_result : ((result [fence,mma,mma] 3).1.ledger.calls[1]?).map (fun call => call.input 0) = some 10 := by rfl
theorem chain_finishes_last_value : declarationLookup "%d0" (result [fence,mma,mma,commit,wait0] 5).1.base.scalar.floats = some (.f32,20) := by rfl
theorem wait_never_replays_old_writeback : declarationLookup "%d0" (result [fence,mma,commit,wait0,overwrite,wait0] 6).1.base.scalar.floats = some (.f32,zero.value) := by rfl
theorem empty_commits_keep_group_identity : (result [fence,commit,commit,wait0] 4).1.ledger.groups = 2 ∧
    (result [fence,commit,commit,wait0] 4).1.ledger.completed = 2 := by decide
theorem acknowledged_recent_group_can_finish :
    (Wgmma.run ctx {oracle with completed := fun _ => 1} [fence,mma,commit,.wgmma (.wait 1),store] 5 seed).toOption.isSome = true := by decide
theorem unrelated_integer_work_can_overlap :
    (Wgmma.run ctx oracle [fence,mma,.ampere (.scalar (.integer (.mov 32 "%tmp" (.imm 7)))),commit,wait0] 5 seed).toOption.isSome = true := by decide
theorem independent_tma_issue_can_overlap :
    (Wgmma.run ctx oracle [fence,mma,.tmaLoad2D ⟨.imm 4096,0⟩ (.imm 8192) (.imm 0) (.imm 0) ⟨.imm 0,0⟩,commit,wait0] 5 seed).toOption.isSome = true := by decide
theorem legacy_entry_refuses_wgmma : Hopper.step ctx oracle.base [fence] {} = .error .wgmmaExtensionRequired := by rfl

end
end Ptx.WgmmaProtocolTests
