import Ptx.Kernels.HopperDoubleBufferLoop

/-! Independent query accounting and origin separation for arbitrary retry
schedules. No memory/protocol admission follows merely from fresh queries. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper

def loopRetryCount (first : Nat) (retries : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => loopRetryCount first retries n+retries (first+n)
def loopPrefetchCount (first tiles : Nat) (leader : Bool) : Nat → Nat
  | 0 => 0
  | n+1 => loopPrefetchCount first tiles leader n+(if needsPrefetch (first+n) tiles leader then 1 else 0)

theorem loopQuery_step_bound (first tiles : Nat) (leader : Bool) (retries : Nat → Nat) (query n : Nat) :
    loopQuery first tiles leader retries query n+retries (first+n)+3 ≤ loopQuery first tiles leader retries query (n+1) := by
  simp only [loopQuery]
  omega

theorem loopQuery_strictMono (first tiles : Nat) (leader : Bool) (retries : Nat → Nat) (query : Nat) :
    StrictMono (loopQuery first tiles leader retries query) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have := loopQuery_step_bound first tiles leader retries query n
  omega

theorem wait_query_intervals_disjoint (first tiles : Nat) (leader : Bool) (retries : Nat → Nat) (query i j : Nat)
    (hij : i < j) :
    loopQuery first tiles leader retries query i+retries (first+i) < loopQuery first tiles leader retries query j := by
  have hnext := loopQuery_step_bound first tiles leader retries query i
  have hmono := (loopQuery_strictMono first tiles leader retries query).monotone (show i+1 ≤ j by omega)
  omega

theorem loopQuery_accounting (first tiles : Nat) (leader : Bool) (retries : Nat → Nat) (query n : Nat) :
    loopQuery first tiles leader retries query n = query+loopRetryCount first retries n+3*n+4*loopPrefetchCount first tiles leader n := by
  induction n with
  | zero => simp [loopQuery,loopRetryCount,loopPrefetchCount]
  | succ n ih =>
    simp only [loopQuery,loopRetryCount,loopPrefetchCount,ih]
    by_cases h : needsPrefetch (first+n) tiles leader <;> simp only [h,ite_true,ite_false] <;> omega

theorem loopPrefetchCount_consumer (first tiles n : Nat) : loopPrefetchCount first tiles false n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [loopPrefetchCount,needsPrefetch,ih]

theorem loopPrefetchCount_bounded (first tiles n : Nat) (leader : Bool) : loopPrefetchCount first tiles leader n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [loopPrefetchCount]
    split <;> omega

theorem loopPrefetchCount_prefix (first tiles n : Nat) (hfirst : first < tiles) (hcount : first+n ≤ tiles) :
    loopPrefetchCount first tiles true n = min n (tiles-first-1) := by
  induction n with
  | zero => simp [loopPrefetchCount]
  | succ n ih =>
    rw [loopPrefetchCount,ih (by omega)]
    by_cases h : needsPrefetch (first+n) tiles true
    · have hlt : first+n+1 < tiles := h.1
      simp only [h,ite_true]
      omega
    · have hge : tiles ≤ first+n+1 := by simpa [needsPrefetch] using h
      simp only [h,ite_false]
      omega

theorem full_loop_prefetch_count (first tiles : Nat) (leader : Bool) (hfirst : first < tiles) :
    loopPrefetchCount first tiles leader (tiles-first) = if leader then tiles-first-1 else 0 := by
  cases leader
  · exact loopPrefetchCount_consumer _ _ _
  · rw [loopPrefetchCount_prefix first tiles (tiles-first) hfirst (by omega)]
    simp

theorem full_loop_query_accounting (first tiles : Nat) (leader : Bool) (retries : Nat → Nat) (query : Nat)
    (hfirst : first < tiles) :
    loopQuery first tiles leader retries query (tiles-first) =
      query+loopRetryCount first retries (tiles-first)+3*(tiles-first)+(if leader then 4*(tiles-first-1) else 0) := by
  rw [loopQuery_accounting,full_loop_prefetch_count first tiles leader hfirst]
  cases leader <;> simp

end Ptx.Kernels.HopperDoubleBuffer
