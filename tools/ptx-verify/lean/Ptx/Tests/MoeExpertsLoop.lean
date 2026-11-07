import Ptx.Kernels.MoeExpertsLoop
import Mathlib.Tactic.NormNum

/-! Actual expert PC=0 entry instances and parameterized data/loop rules.
These local witnesses do not establish launch-wide memory consistency. -/
namespace Ptx.MoeExpertsLoopTests
open Ptx.ISA Ptx.Scalar Ptx.MoeExpertsLoop
noncomputable section
set_option maxHeartbeats 2000000

def ctx : Scalar.Context := {
  id := ⟨⟨1,1,0⟩,.zero⟩, block := ⟨2,2,1⟩
  params := [("X",0),("W",64),("R",128),("H",256),("M",3),("N",3),("K",2)]
}
def routed (expert : Nat) (tail : Scalar.Oracle) : Scalar.Oracle :=
  fun query => if query = 0 then .integer expert else tail (query-1)
def entry (expert fuel : Nat) : Scalar.State :=
  ((Scalar.run ctx (routed expert (fun _ => .integer 0)) code fuel {}).toOption.map Prod.fst).getD {}
def one : Scalar.State := entry 1 46
def zero : Scalar.State := entry 0 40
def layout (expert : Fin 2) : Layout := {
  count := 2, aBase := 16, bBase := 72+24*(expert : Nat), stride := 12, output := 288+36*(expert : Nat)
  count32 := by decide
  output64 := by have := expert.isLt; omega
  aRead64 := by intro k hk; omega
  bRead64 := by intro k hk; have := expert.isLt; omega
}

set_option maxRecDepth 8000 in
theorem prefix_one (tail : Scalar.Oracle) : Scalar.run ctx (routed 1 tail) code 46 {} =
    .ok (one,[.read ⟨.global,136⟩ (u32Bytes 1)]) := rfl
set_option maxRecDepth 8000 in
theorem prefix_zero (tail : Scalar.Oracle) : Scalar.run ctx (routed 0 tail) code 40 {} =
    .ok (zero,[.read ⟨.global,136⟩ (u32Bytes 0)]) := rfl

set_option maxRecDepth 8000 in
theorem entry_one : FmaLoop.Inv 46 1 (layout 1) 0 0 one := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change some (Symbolic.Format.f32,(F32Literal.mk 0 (by decide) (by decide)).value) = some (Symbolic.Format.f32,(0 : ℝ))
    simp only [F32Literal.zero_value]
  · exact run_banks_disjoint (prefix_one (fun _ => .integer 0)) empty_banks_disjoint
set_option maxRecDepth 8000 in
theorem entry_zero : FmaLoop.Inv 46 1 (layout 0) 0 0 zero := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change some (Symbolic.Format.f32,(F32Literal.mk 0 (by decide) (by decide)).value) = some (Symbolic.Format.f32,(0 : ℝ))
    simp only [F32Literal.zero_value]
  · exact run_banks_disjoint (prefix_zero (fun _ => .integer 0)) empty_banks_disjoint

def dataOracle (x : Moe.Matrix) (weights : Moe.Weights) (expert : Nat) : Scalar.Oracle :=
  fun query => .real .f32 (if query%2 = 0 then x 2 (query/2) else weights expert (query/2) 2)
theorem data_even (x : Moe.Matrix) (weights : Moe.Weights) (expert k : Nat) :
    routed expert (dataOracle x weights expert) (1+2*k) = .real .f32 (x 2 k) := by
  have hnonzero : 1+2*k ≠ 0 := by omega
  have hdiv : (2*k)/2 = k := by omega
  have hmod : (2*k)%2 = 0 := by omega
  simp [routed,dataOracle,hnonzero,hdiv,hmod]
theorem data_odd (x : Moe.Matrix) (weights : Moe.Weights) (expert k : Nat) :
    routed expert (dataOracle x weights expert) (1+2*k+1) = .real .f32 (weights expert k 2) := by
  have hnonzero : 1+2*k+1 ≠ 0 := by omega
  have hsub : 1+2*k+1-1 = 2*k+1 := by omega
  have hdiv : (2*k+1)/2 = k := by omega
  have hmod : (2*k+1)%2 ≠ 0 := by omega
  simp [routed,dataOracle,hnonzero,hsub,hdiv,hmod]

theorem actual_one_all_data (x : Moe.Matrix) (weights : Moe.Weights) : ∃ last,
    Scalar.run ctx (routed 1 (dataOracle x weights 1)) code 68 {} = .ok
      (last,[.read ⟨.global,136⟩ (u32Bytes 1)] ++
        FmaLoop.loopReads (layout 1) x (expertMatrix weights 1) 2 2 0 2 ++
        [.write ⟨.global,324⟩ (Symbolic.encode .f32 (Moe.linear x weights 1 2 2 2))]) ∧
      last.core.thread.status = .done ∧ last.core.queries = 5 := by
  obtain ⟨last,hr,hf⟩ := complete (layout 1) ctx (routed 1 (dataOracle x weights 1)) x weights 1 2 2
    (fun k _ => data_even x weights 1 k) (fun k _ => data_odd x weights 1 k) entry_one
  have hfull := Scalar.run_append (prefix_one (dataOracle x weights 1)) hr
  exact ⟨last,by simpa [layout,List.append_assoc] using hfull,hf.done,hf.queries⟩
theorem actual_zero_all_data (x : Moe.Matrix) (weights : Moe.Weights) : ∃ last,
    Scalar.run ctx (routed 0 (dataOracle x weights 0)) code 62 {} = .ok
      (last,[.read ⟨.global,136⟩ (u32Bytes 0)] ++
        FmaLoop.loopReads (layout 0) x (expertMatrix weights 0) 2 2 0 2 ++
        [.write ⟨.global,288⟩ (Symbolic.encode .f32 (Moe.linear x weights 0 2 2 2))]) ∧
      last.core.thread.status = .done ∧ last.core.queries = 5 := by
  obtain ⟨last,hr,hf⟩ := complete (layout 0) ctx (routed 0 (dataOracle x weights 0)) x weights 0 2 2
    (fun k _ => data_even x weights 0 k) (fun k _ => data_odd x weights 0 k) entry_zero
  have hfull := Scalar.run_append (prefix_zero (dataOracle x weights 0)) hr
  exact ⟨last,by simpa [layout,List.append_assoc] using hfull,hf.done,hf.queries⟩

theorem arbitrary_completed_loop (oracle : Scalar.Oracle) {n last events}
    (hr : Scalar.run ctx oracle code n one = .ok (last,events)) (hd : last.core.thread.status = .done) :
    n = 22 ∧ events = FmaLoop.loopReads (layout 1) (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 0 2 ++
      [.write ⟨.global,324⟩ (Symbolic.encode .f32
        (ScalarMatmul.prefixProduct (FmaLoop.replyA 1 oracle) (FmaLoop.replyB 1 oracle) 0 0 2))] := by
  have h := reconstruct (layout 1) ctx oracle entry_one hr hd
  exact ⟨h.1,h.2.1⟩
theorem query_origin_cannot_reset : ¬ FmaLoop.Inv 46 0 (layout 1) 0 0 one := by
  intro h
  have hq := h.queries
  change (1 : Nat) = 0 at hq
  omega
theorem integer_float_reply_rejected (oracle : Scalar.Oracle) (hq : oracle 1 = .integer 99) :
    ¬ ∃ n last events, Scalar.run ctx oracle code n one = .ok (last,events) ∧ last.core.thread.status = .done := by
  rintro ⟨n,last,events,hr,hd⟩
  exact FmaLoop.completed_wrong_type_rejected fragment (layout 1) ctx oracle entry_one (by decide) hq hr hd

theorem wrong_format_reply_rejected (oracle : Scalar.Oracle) (value : ℝ) (hq : oracle 1 = .real .f64 value) :
    ¬ ∃ n last events, Scalar.run ctx oracle code n one = .ok (last,events) ∧ last.core.thread.status = .done := by
  rintro ⟨n,last,events,hr,hd⟩
  obtain ⟨a,b,ha,hb⟩ := FmaLoop.completed_iteration_replies fragment (layout 1) ctx oracle entry_one (by decide) hr hd
  simp only [Nat.mul_zero,Nat.add_zero,hq] at ha
  cases ha

def badBranch : List Scalar.Instr := code.set 47 (.integer (.branch "%p" true 54))
theorem bad_branch_certificate_rejected : ¬ FmaLoop.Fragment badBranch 46 := by
  intro h
  have hb := h.branch
  change some (.integer (.branch "%p" true 54) : Scalar.Instr) = some (.integer (.branch "%p" true 55)) at hb
  cases hb
def missingStore : List Scalar.Instr := code.set 55 (.integer .ret)
theorem missing_store_certificate_rejected : ¬ FmaLoop.Fragment missingStore 46 := by
  intro h
  have hs := h.store
  change some (.integer .ret : Scalar.Instr) = some (.store .f32 .global {base := .reg "%cp"} (.reg "%acc")) at hs
  cases hs

def changedPrefix : List Scalar.Instr := code.set 0 (.integer .ret)
/-- A loop certificate alone cannot prove entry correctness. This program has
the same certified loop but returns before any routing or expert work. -/
theorem fragment_does_not_certify_entry : FmaLoop.Fragment changedPrefix 46 ∧
    ∃ last, Scalar.run ctx (fun _ => .integer 0) changedPrefix 1 {} = .ok (last,[]) ∧
      last.core.thread.status = .done := by
  constructor
  · constructor <;> rfl
  · exact ⟨{core := {thread := {status := .done}}},rfl,rfl⟩


def zeroCtx : Scalar.Context := {
  ctx with params := [("X",256),("W",256),("R",128),("H",256),("M",3),("N",3),("K",0)]
}
def emptyEntry : Scalar.State :=
  ((Scalar.run zeroCtx (routed 1 (fun _ => .integer 0)) code 46 {}).toOption.map Prod.fst).getD {}
def emptyLayout : Layout := {
  count := 0,aBase := 256,bBase := 264,stride := 12,output := 324
  count32 := by decide,output64 := by decide
  aRead64 := by intro k hk; omega
  bRead64 := by intro k hk; omega
}
set_option maxRecDepth 8000 in
theorem empty_prefix (tail : Scalar.Oracle) : Scalar.run zeroCtx (routed 1 tail) code 46 {} =
    .ok (emptyEntry,[.read ⟨.global,136⟩ (u32Bytes 1)]) := rfl
set_option maxRecDepth 8000 in
theorem empty_entry : FmaLoop.Inv 46 1 emptyLayout 0 0 emptyEntry := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change some (Symbolic.Format.f32,(F32Literal.mk 0 (by decide) (by decide)).value) = some (Symbolic.Format.f32,(0 : ℝ))
    simp only [F32Literal.zero_value]
  · exact run_banks_disjoint (empty_prefix (fun _ => .integer 0)) empty_banks_disjoint

theorem empty_alias_no_float_reads (tail : Scalar.Oracle) : ∃ last,
    Scalar.run zeroCtx (routed 1 tail) code 50 {} = .ok
      (last,[.read ⟨.global,136⟩ (u32Bytes 1),.write ⟨.global,324⟩ (Symbolic.encode .f32 0)]) ∧
      last.core.thread.status = .done ∧ last.core.queries = 1 := by
  have hi : FmaLoop.Inv 46 1 emptyLayout emptyLayout.count 0 emptyEntry := empty_entry
  obtain ⟨last,hr,hf⟩ := FmaLoop.finish fragment emptyLayout zeroCtx (routed 1 tail) hi
  have hfull := Scalar.run_append (empty_prefix tail) hr
  exact ⟨last,by simpa [emptyLayout] using hfull,hf.done,hf.queries⟩

end
end Ptx.MoeExpertsLoopTests
