import Ptx.Generated.CpAsyncCopy
import Ptx.Generated.CpAsyncGroups
import Ptx.Generated.CpAsyncNoWait
import Ptx.Ampere.Source
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-! Actual generated source traces and augmented copy identities. These tests
exercise group visibility, not an as-yet-unproved rf/co memory-value contract. -/
namespace Ptx.AmpereTests
open Ptx.ISA Ptx.Ampere
noncomputable section

def id : ThreadId := ⟨.zero,.zero⟩
def geometry : Geometry := ⟨.one,.one⟩
def params : Bindings := [("X",64),("Y",128)]
def ctx : Scalar.Context := {id := id,params := params,block := .one}
def wordBytes (value : Nat) : List Symbolic.Byte := (encodeU32 value).map Symbolic.Byte.bits
def payload : List Symbolic.Byte := wordBytes 7 ++ wordBytes 4294967295 ++ wordBytes 42 ++ wordBytes 99
def oracle : Oracle := ⟨fun q => .integer (if q = 1 then 7 else if q = 2 then 4294967295 else if q = 3 then 42 else 99),fun _ => payload,fun _ => .integer 0,fun _ _ => 0⟩
def runResult (code : List Ampere.Instr) (count : Nat) (o : Oracle) : State × List Event :=
  ((Ampere.run ctx o code count {}).toOption).getD ({},[])
def trace (code : List Ampere.Instr) (count : Nat) (o : Oracle) : ThreadTrace :=
  ⟨id,o,count,(runResult code count o).1,(runResult code count o).2⟩
def goodTrace : ThreadTrace := trace Generated.cp_async_copy.program 15 oracle
def badTrace : ThreadTrace := trace Generated.cp_async_no_wait.program 8 oracle
def good : Candidate := ⟨[goodTrace]⟩
def bad : Candidate := ⟨[badTrace]⟩
def launch : Scalar.Launch := ⟨geometry,params,fun _ => .bits (byte 165)⟩
def operation : CopyId := ⟨id,0⟩
def copy : Copy := ⟨.cg,0,⟨.global,64⟩,⟨.shared .zero,0⟩,payload⟩
def event (serial : Nat) : Ptx.Event.EventId := ⟨id,serial⟩

theorem good_source : Produced Generated.cp_async_copy.program params .one goodTrace := by rfl
theorem bad_source : Produced Generated.cp_async_no_wait.program params .one badTrace := by rfl
theorem good_done : goodTrace.final.scalar.core.thread.status = .done := by rfl
theorem bad_done : badTrace.final.scalar.core.thread.status = .done := by rfl
theorem id_valid : id.Valid geometry := by norm_num [id,geometry,ThreadId.Valid,Dim3.Within,Dim3.zero,Dim3.one]
theorem only_thread {thread : ThreadId} (hv : thread.Valid geometry) : thread = id := by
  rcases thread with ⟨⟨cx,cy,cz⟩,⟨tx,ty,tz⟩⟩
  simp only [geometry,ThreadId.Valid,Dim3.Within,Dim3.one] at hv
  have hx : cx = 0 := by omega
  have hy : cy = 0 := by omega
  have hz : cz = 0 := by omega
  have htx : tx = 0 := by omega
  have hty : ty = 0 := by omega
  have htz : tz = 0 := by omega
  subst_vars
  rfl

theorem good_wellFormed : WellFormed Generated.cp_async_copy.program launch good := by
  refine ⟨by norm_num [launch,geometry,Geometry.Valid,Dim3.Positive,Dim3.one],by simp [good],?_,?_⟩
  · intro t ht
    have he : t = goodTrace := List.mem_singleton.mp ht
    subst t
    exact ⟨id_valid,good_source⟩
  · intro thread hv
    have hid := only_thread hv
    exact ⟨goodTrace,List.mem_singleton_self _,hid.symm⟩
theorem bad_wellFormed : WellFormed Generated.cp_async_no_wait.program launch bad := by
  refine ⟨by norm_num [launch,geometry,Geometry.Valid,Dim3.Positive,Dim3.one],by simp [bad],?_,?_⟩
  · intro t ht
    have he : t = badTrace := List.mem_singleton.mp ht
    subst t
    exact ⟨id_valid,bad_source⟩
  · intro thread hv
    have hid := only_thread hv
    exact ⟨badTrace,List.mem_singleton_self _,hid.symm⟩

theorem good_issued : good.eventAt (event 0) = some (.issue 0 copy) := by rfl
theorem good_copy : good.copyAt operation = some copy := event_issue_has_copy good_wellFormed good_issued
theorem copy_is_not_ordinary_store : good.memoryKind (.thread (event 0)) = none := by rfl
theorem pending_copy_queries : goodTrace.final.scalar.core.queries = 5 := by rfl
theorem independent_copy_footprint : good.memoryKind (.copyWrite operation) = some (.write ⟨.shared .zero,0⟩ payload) := by rfl
theorem good_covers : WaitCovers good operation (event 2) := ⟨rfl,copy,1,0,good_copy,rfl,by decide⟩
theorem good_copy_publication : BaseOrder good (.copyWrite operation) (.thread (event 5)) := by
  apply publish_after_wait_and_barrier good_covers
    (arrive := event 3) (leave := event 4)
  · exact ⟨rfl,rfl,rfl,by decide⟩
  · exact ⟨rfl,0,0,rfl,rfl⟩
  · exact ⟨rfl,rfl,rfl,by decide⟩

theorem bad_no_wait (waitEvent : Ptx.Event.EventId) : ¬ WaitCovers bad operation waitEvent := by
  rintro ⟨hid,op,groups,keep,_,hwait,_⟩
  rcases waitEvent with ⟨thread,serial⟩
  change thread = id at hid
  subst thread
  have hb : serial < badTrace.events.length := by
    have hh : badTrace.events[serial]? = some (.wait groups keep) := hwait
    exact (List.getElem?_eq_some_iff.mp hh).1
  change serial < 6 at hb
  interval_cases serial <;> cases hwait
theorem barrier_without_wait_has_no_copy_publication :
    ¬ BaseOrder bad (.copyWrite operation) (.thread (event 4)) := no_wait_no_copy_order bad_no_wait

def groupOracle : Oracle := ⟨fun _ => .integer 0,fun q => if q < 2 then wordBytes 7 else wordBytes 42 ++ wordBytes 99,fun _ => .integer 0,fun _ _ => 0⟩
def groupTrace : ThreadTrace := trace Generated.cp_async_groups.program 10 groupOracle
def groups : Candidate := ⟨[groupTrace]⟩
def opId (ordinal : Nat) : CopyId := ⟨id,ordinal⟩
theorem groups_source : Produced Generated.cp_async_groups.program params .one groupTrace := by rfl
theorem groups_done : groupTrace.final.scalar.core.thread.status = .done := by rfl
theorem groups_count : groupTrace.final.groups = 3 ∧ groupTrace.final.copies.length = 3 := by exact ⟨rfl,rfl⟩
theorem wait_one_covers_old : WaitCovers groups (opId 0) (event 5) := ⟨rfl,_,2,1,rfl,rfl,by decide⟩
theorem wait_one_leaves_recent : ¬ WaitCovers groups (opId 1) (event 5) :=
  recent_group_not_covered (op := ⟨.ca,1,⟨.global,68⟩,⟨.shared .zero,4⟩,wordBytes 7⟩) rfl rfl (by decide)
theorem wait_zero_leaves_open : ¬ WaitCovers groups (opId 2) (event 6) :=
  open_group_not_covered (op := ⟨.ca,2,⟨.global,72⟩,⟨.shared .zero,8⟩,wordBytes 42 ++ wordBytes 99⟩) rfl rfl (by decide)
theorem wait_all_covers_open : WaitCovers groups (opId 2) (event 8) := ⟨rfl,_,3,0,rfl,rfl,by decide⟩

theorem same_group_writes_not_in_issuer_po : ¬ ProgramOrder good (.copyWrite operation) (.thread (event 1)) :=
  (copy_write_outside_program_order good operation _).1

def shortOracle : Oracle := ⟨oracle.scalar,fun _ => wordBytes 7,fun _ => .integer 0,fun _ _ => 0⟩
theorem short_payload_rejected :
    (Ampere.run ctx shortOracle Generated.cp_async_copy.program 3 {}).toOption = none := by rfl

end
end Ptx.AmpereTests
