import Ptx.Kernels.HopperDoubleBufferPrefetchGuard
import Ptx.Hopper.WgmmaIssueRules

/-! Actual PCs 76..79, retaining arbitrary call history and arithmetic replies.
The read-accumulator hypothesis constrains source register availability, not
matrix results. Tensor/byte/collective admission must independently constrain
captured arithmetic and operand replies before asserting GEMM correctness. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def computeFence (s : Wgmma.State) : Wgmma.State := {
  base := Ampere.advance s.base
  ledger := {s.ledger with fenced := true,dirty := [],syncs := s.ledger.syncs+1}
}
def computeCall (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (pa pb : Nat) (input : Fin 4 → ℝ) : Wgmma.Call :=
  Wgmma.makeCall ctx (computeFence s) oracle ⟨"%d0","%d1","%d2","%d3"⟩ pa pb true input
def computeIssued (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (pa pb : Nat) (input : Fin 4 → ℝ) : Wgmma.State :=
  Wgmma.issueState (computeFence s) (computeCall ctx oracle s pa pb input)
def computeCommitted (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (pa pb : Nat) (input : Fin 4 → ℝ) : Wgmma.State :=
  let issued := computeIssued ctx oracle s pa pb input
  {base := Ampere.advance issued.base,
   ledger := {issued.ledger with groups := issued.ledger.groups+1,syncs := issued.ledger.syncs+1}}
def computeState (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (pa pb : Nat) (input : Fin 4 → ℝ) : Wgmma.State :=
  let committed := computeCommitted ctx oracle s pa pb input
  Wgmma.waitState committed 0 (oracle.completed committed.base.scalar.core.queries)
def computeEvents (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (pa pb : Nat) (input : Fin 4 → ℝ) : List Wgmma.Event :=
  [.fence (Wgmma.mark ctx s),
   .mma (Wgmma.mark ctx (computeFence s)) (computeCall ctx oracle s pa pb input),
   .commit (Wgmma.mark ctx (computeIssued ctx oracle s pa pb input)) s.ledger.groups,
   .wait (Wgmma.mark ctx (computeCommitted ctx oracle s pa pb input)) (s.ledger.groups+1) 0
     s.ledger.completed (computeState ctx oracle s pa pb input).ledger.completed (s.base.scalar.core.queries+1)]

theorem compute_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle) (s : Wgmma.State)
    (pa pb : Nat) (input : Fin 4 → ℝ)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 76)
    (ha : lookup "%ad" s.base.scalar.core.thread.regs = some pa)
    (hb : lookup "%bd" s.base.scalar.core.thread.regs = some pb)
    (hin : Wgmma.readScaledAccumulator (computeFence s) ⟨"%d0","%d1","%d2","%d3"⟩ 1 = .ok input) :
    Wgmma.run ctx oracle code 4 s = .ok (computeState ctx oracle s pa pb input,computeEvents ctx oracle s pa pb input) := by
  have h0 : Wgmma.step ctx oracle code s = .ok (computeFence s,[.fence (Wgmma.mark ctx s)]) :=
    Wgmma.fence_does_not_complete hr (by simp [hpc,code,Generated.hopper_double_buffer_gemm.program])
  have h1 : Wgmma.step ctx oracle code (computeFence s) = .ok
      (computeIssued ctx oracle s pa pb input,[.mma (Wgmma.mark ctx (computeFence s)) (computeCall ctx oracle s pa pb input)]) := by
    apply Wgmma.mma_execute (a := "%ad") (b := "%bd") (scaleD := .imm 1) (by simpa [computeFence,Ampere.advance,Ptx.advance] using hr)
      (by simp [computeFence,Ampere.advance,Ptx.advance,hpc,code,Generated.hopper_double_buffer_gemm.program])
      rfl (by decide) (by simp [computeFence])
      (by simp [Ptx.eval,computeFence,Ampere.advance,Ptx.advance,ha])
      (by simp [Ptx.eval,computeFence,Ampere.advance,Ptx.advance,hb]) rfl hin
  have h2 : Wgmma.step ctx oracle code (computeIssued ctx oracle s pa pb input) = .ok
      (computeCommitted ctx oracle s pa pb input,
        [.commit (Wgmma.mark ctx (computeIssued ctx oracle s pa pb input)) s.ledger.groups]) := by
    exact Wgmma.commit_creates_distinct_group (by simpa [computeIssued,Wgmma.issueState,computeFence,Ampere.advance,Ptx.advance] using hr)
      (by simp [computeIssued,Wgmma.issueState,computeFence,Ampere.advance,Ptx.advance,hpc,code,Generated.hopper_double_buffer_gemm.program])
  have h3 : Wgmma.step ctx oracle code (computeCommitted ctx oracle s pa pb input) = .ok
      (computeState ctx oracle s pa pb input,
        [.wait (Wgmma.mark ctx (computeCommitted ctx oracle s pa pb input)) (s.ledger.groups+1) 0
          s.ledger.completed (computeState ctx oracle s pa pb input).ledger.completed (s.base.scalar.core.queries+1)]) := by
    have hrun : (computeCommitted ctx oracle s pa pb input).base.scalar.core.thread.status = .running := by
      simpa [computeCommitted,computeIssued,Wgmma.issueState,computeFence,Ampere.advance,Ptx.advance] using hr
    have hfetch : code[(computeCommitted ctx oracle s pa pb input).base.scalar.core.thread.pc]? = some (.wgmma (.wait 0)) := by
      simp [computeCommitted,computeIssued,Wgmma.issueState,computeFence,Ampere.advance,Ptx.advance,hpc,code,Generated.hopper_double_buffer_gemm.program]
    simp only [Wgmma.step,hrun,hfetch,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,ite_false,
      bind,Except.bind,pure,Except.pure]
    rfl
  simp only [Wgmma.run,h0,h1,h2,h3,Except.bind,List.nil_append,List.cons_append,List.append_nil,computeEvents]

@[simp] theorem computeState_groups (ctx oracle s pa pb input) :
    (computeState ctx oracle s pa pb input).ledger.groups = s.ledger.groups+1 := rfl
@[simp] theorem computeState_calls (ctx oracle s pa pb input) :
    (computeState ctx oracle s pa pb input).ledger.calls = s.ledger.calls++[computeCall ctx oracle s pa pb input] := rfl
@[simp] theorem computeState_queries (ctx oracle s pa pb input) :
    (computeState ctx oracle s pa pb input).base.scalar.core.queries = s.base.scalar.core.queries+2 := rfl
@[simp] theorem computeState_syncs (ctx oracle s pa pb input) :
    (computeState ctx oracle s pa pb input).ledger.syncs = s.ledger.syncs+4 := rfl

theorem computeState_completed (ctx oracle s pa pb input) (hc : s.ledger.completed ≤ s.ledger.groups) :
    (computeState ctx oracle s pa pb input).ledger.completed = s.ledger.groups+1 := by
  exact Wgmma.wait_zero_completes_committed (Nat.le_trans hc (Nat.le_succ _))

theorem computeState_no_pending (ctx oracle s pa pb input)
    (hc : s.ledger.completed ≤ s.ledger.groups) (hp : Wgmma.pending s.ledger = []) :
    Wgmma.pending (computeState ctx oracle s pa pb input).ledger = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro call hm
  change call ∈ s.ledger.calls++[computeCall ctx oracle s pa pb input] at hm
  simp only [List.mem_append,List.mem_singleton] at hm
  simp only [decide_eq_true_eq]
  rw [computeState_completed ctx oracle s pa pb input hc]
  intro hbad
  rcases hm with hm | rfl
  · have hn : ¬s.ledger.completed ≤ call.group := by
      intro h
      have hm' : call ∈ Wgmma.pending s.ledger := List.mem_filter.mpr ⟨hm,by simpa using h⟩
      simpa [hp] using hm'
    omega
  · change s.ledger.groups+1 ≤ s.ledger.groups at hbad
    omega

theorem compute_only_finishing (ctx oracle s pa pb input)
    (hc : s.ledger.completed ≤ s.ledger.groups) (hp : Wgmma.pending s.ledger = []) :
    (computeCommitted ctx oracle s pa pb input).ledger.calls.filter
      (fun call => decide ((computeCommitted ctx oracle s pa pb input).ledger.completed ≤ call.group ∧
        call.group < Wgmma.completionCut (computeCommitted ctx oracle s pa pb input).ledger 0
          (oracle.completed (computeCommitted ctx oracle s pa pb input).base.scalar.core.queries))) =
      [computeCall ctx oracle s pa pb input] := by
  have hcut : Wgmma.completionCut (computeCommitted ctx oracle s pa pb input).ledger 0
      (oracle.completed (computeCommitted ctx oracle s pa pb input).base.scalar.core.queries) = s.ledger.groups+1 :=
    Wgmma.wait_zero_completes_committed (Nat.le_trans hc (Nat.le_succ _))
  rw [hcut]
  change (s.ledger.calls++[computeCall ctx oracle s pa pb input]).filter
    (fun call => decide (s.ledger.completed ≤ call.group ∧ call.group < s.ledger.groups+1)) = _
  rw [List.filter_append]
  have hold : s.ledger.calls.filter (fun call => decide (s.ledger.completed ≤ call.group ∧ call.group < s.ledger.groups+1)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro call hm
    simp only [decide_eq_true_eq]
    intro h
    have hm' : call ∈ Wgmma.pending s.ledger := List.mem_filter.mpr ⟨hm,by simpa using h.1⟩
    simpa [hp] using hm'
  rw [hold]
  simp [computeCall,Wgmma.makeCall,computeFence,hc]

theorem computeState_pc (ctx oracle s pa pb input)
    (hc : s.ledger.completed ≤ s.ledger.groups) (hp : Wgmma.pending s.ledger = []) :
    (computeState ctx oracle s pa pb input).base.scalar.core.thread.pc = s.base.scalar.core.thread.pc+4 := by
  simp only [computeState,Wgmma.waitState,compute_only_finishing ctx oracle s pa pb input hc hp,
    List.foldl_cons,List.foldl_nil]
  rfl

theorem computeState_status (ctx oracle s pa pb input)
    (hc : s.ledger.completed ≤ s.ledger.groups) (hp : Wgmma.pending s.ledger = []) :
    (computeState ctx oracle s pa pb input).base.scalar.core.thread.status = s.base.scalar.core.thread.status := by
  simp only [computeState,Wgmma.waitState,compute_only_finishing ctx oracle s pa pb input hc hp,
    List.foldl_cons,List.foldl_nil]
  rfl

def computeSlotName (i : Fin 4) : String :=
  if i.val = 0 then "%d0" else if i.val = 1 then "%d1" else if i.val = 2 then "%d2" else "%d3"

theorem computeState_accumulators (ctx oracle s pa pb input)
    (hc : s.ledger.completed ≤ s.ledger.groups) (hp : Wgmma.pending s.ledger = []) (i : Fin 4) :
    declarationLookup (computeSlotName i) (computeState ctx oracle s pa pb input).base.scalar.floats =
      some (.f32,oracle.matrix s.base.scalar.core.queries i) ∧
    lookup (computeSlotName i) (computeState ctx oracle s pa pb input).base.scalar.core.thread.regs = none := by
  simp only [computeState,Wgmma.waitState,compute_only_finishing ctx oracle s pa pb input hc hp,
    List.foldl_cons,List.foldl_nil]
  constructor
  · fin_cases i <;>
      simp [computeSlotName,Wgmma.writeResult,computeCall,Wgmma.makeCall,computeCommitted,computeIssued,
        Wgmma.issueState,computeFence,Ampere.advance,Ptx.advance,declarationLookup,Ampere.Registers4.names]
  · change lookup (computeSlotName i) (s.base.scalar.core.thread.regs.filter
      (fun kv => !(["%d0","%d1","%d2","%d3"] : List String).contains kv.1)) = none
    rw [Ampere.integer_lookup_filter (computeSlotName i)
      (fun key => !(["%d0","%d1","%d2","%d3"] : List String).contains key) s.base.scalar.core.thread.regs]
    fin_cases i <;> simp [computeSlotName]

theorem computeState_nat_frame (ctx oracle s pa pb input)
    (hc : s.ledger.completed ≤ s.ledger.groups) (hp : Wgmma.pending s.ledger = []) (name : String)
    (hn : name ∉ ["%d0","%d1","%d2","%d3"]) :
    lookup name (computeState ctx oracle s pa pb input).base.scalar.core.thread.regs = lookup name s.base.scalar.core.thread.regs := by
  simp only [computeState,Wgmma.waitState,compute_only_finishing ctx oracle s pa pb input hc hp,
    List.foldl_cons,List.foldl_nil]
  change lookup name (s.base.scalar.core.thread.regs.filter
    (fun kv => !(["%d0","%d1","%d2","%d3"] : List String).contains kv.1)) = _
  rw [Ampere.integer_lookup_filter name
    (fun key => !(["%d0","%d1","%d2","%d3"] : List String).contains key) s.base.scalar.core.thread.regs]
  simp [hn]

theorem compute_and_advance_execute (ctx : Scalar.Context) (oracle : Wgmma.Oracle)
    (s : Wgmma.State) (pa pb : Nat) (input : Fin 4 → ℝ) (tile tiles : Nat)
    (hr : s.base.scalar.core.thread.status = .running) (hpc : s.base.scalar.core.thread.pc = 76)
    (ha : lookup "%ad" s.base.scalar.core.thread.regs = some pa)
    (hb : lookup "%bd" s.base.scalar.core.thread.regs = some pb)
    (hin : Wgmma.readScaledAccumulator (computeFence s) ⟨"%d0","%d1","%d2","%d3"⟩ 1 = .ok input)
    (hc : s.ledger.completed ≤ s.ledger.groups) (hp : Wgmma.pending s.ledger = [])
    (hs : lookup "%slot" s.base.scalar.core.thread.regs = some (tile%2))
    (ht : lookup "%tile" s.base.scalar.core.thread.regs = some tile)
    (hts : lookup "%tiles" s.base.scalar.core.thread.regs = some tiles)
    (hlt : tile < tiles) (hbound : tiles < 2^32) :
    Wgmma.run ctx oracle code 9 s = .ok
      (advanceState (computeState ctx oracle s pa pb input) tile tiles,
        computeEvents ctx oracle s pa pb input++advanceEvents (computeState ctx oracle s pa pb input)) := by
  have hn := compute_execute ctx oracle s pa pb input hr hpc ha hb hin
  have ht' := advance_execute ctx oracle (computeState ctx oracle s pa pb input) tile tiles
    (by rwa [computeState_status ctx oracle s pa pb input hc hp])
    (by rw [computeState_pc ctx oracle s pa pb input hc hp,hpc])
    (computeState_no_pending ctx oracle s pa pb input hc hp)
    (by rwa [computeState_nat_frame ctx oracle s pa pb input hc hp "%slot" (by decide)])
    (by rwa [computeState_nat_frame ctx oracle s pa pb input hc hp "%tile" (by decide)])
    (by rwa [computeState_nat_frame ctx oracle s pa pb input hc hp "%tiles" (by decide)]) hlt hbound
  rw [show 9 = 4+5 from rfl,Wgmma.run_add,hn]
  simp only [Except.bind,ht']

end
end Ptx.Kernels.HopperDoubleBuffer
