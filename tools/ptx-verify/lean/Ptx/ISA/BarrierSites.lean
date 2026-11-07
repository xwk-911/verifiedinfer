import Ptx.ISA.Syntax

/-! A sufficient, local source certificate: a barrier ID occurs at one static
PC. This is not a general convergence checker; valid programs may use multiple
sites at different generations. Generic event predicates do not yet encode the
full PTX aligned-barrier instruction/warp legality requirements. -/
namespace Ptx.ISA

def barrierSites (code : List Ptx.Instr) (bid : Nat) : List Nat :=
  (List.range code.length).filter (fun pc => match code[pc]? with
    | some (.barrier actual) => actual == bid
    | _ => false)

def uniqueBarrierSites (code : List Ptx.Instr) : Bool :=
  (List.range code.length).all fun a => (List.range code.length).all fun b =>
    match code[a]?,code[b]? with
    | some (.barrier x),some (.barrier y) => !(x == y) || a == b
    | _,_ => true

theorem unique_barrier_sites {code : List Ptx.Instr} {a b bid : Nat} (hu : uniqueBarrierSites code = true)
    (ha : code[a]? = some (Ptx.Instr.barrier bid)) (hb : code[b]? = some (Ptx.Instr.barrier bid)) : a = b := by
  have h := List.all_eq_true.mp hu a (List.mem_range.mpr (List.getElem?_eq_some_iff.mp ha).1)
  have h' := List.all_eq_true.mp h b (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hb).1)
  simpa [ha,hb] using h'

theorem barrier_site_mem {code bid pc} (h : code[pc]? = some (Ptx.Instr.barrier bid)) :
    pc ∈ barrierSites code bid := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr (List.getElem?_eq_some_iff.mp h).1,by simp [h]⟩

theorem single_barrier_site {code bid pc site} (hs : barrierSites code bid = [site])
    (h : code[pc]? = some (Ptx.Instr.barrier bid)) : pc = site := by
  have hm := barrier_site_mem h
  rw [hs] at hm
  simpa using hm

end Ptx.ISA
