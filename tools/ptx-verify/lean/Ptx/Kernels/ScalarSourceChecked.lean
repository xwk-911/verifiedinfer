import Ptx.Scalar.Checked
import Ptx.Kernels.ScalarMatmulWitness
import Ptx.Kernels.ScalarAttentionWitness
import Ptx.Kernels.AtomicDispatchWitness
import Ptx.Kernels.AtomicDispatchOutput
import Ptx.Kernels.FloatLiteralsUniversal

/-! Existing scalar contracts and independent complete witnesses lifted into
source-aware admission. Actual source certificates discharge alignment, with no
new caller assumptions or weaker output/frame specifications. -/
namespace Ptx.ScalarMatmulEvent
open Ptx.ISA Ptx.Scalar Ptx.ScalarMatmul
noncomputable section

theorem checked_sites : Scalar.uniqueBarrierSites code = true := by decide
theorem checked_correct (cfg : Config) (a b : Matrix) (domain : List Location) (hcover : CoversOutput cfg domain) :
    Scalar.CheckedTriple code (Pre cfg a b) (fun _ => domain)
      (fun launch output => Post a b cfg.input.m cfg.input.n cfg.input.k cfg.input.c output ∧
        ∀ loc ∈ domain, ¬ InWords cfg.input.c (cfg.input.m*cfg.input.n) loc → output loc = launch.initial loc) :=
  Scalar.triple_checked (correct cfg a b domain hcover)
theorem checked_nonvacuous (cfg : Config) (a b : Matrix) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    Scalar.CheckedNonvacuous code (Pre cfg a b) (fun _ => domain) :=
  Scalar.nonvacuous_checked_of_unique_sites checked_sites (nonvacuous cfg a b domain hglobal)

end
end Ptx.ScalarMatmulEvent

namespace Ptx.ScalarAttentionEvent
open Ptx.ISA Ptx.Scalar Ptx.ScalarAttention
noncomputable section

theorem checked_sites : Scalar.uniqueBarrierSites code = true := by decide
theorem checked_correct (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ)
    (domain : List Location) (hcover : CoversOutput cfg domain) :
    Scalar.CheckedTriple code (Pre cfg q key value scale) (fun _ => domain)
      (fun launch output => Attention.Post q key value (Real.log 2*scale) cfg.input.m cfg.input.n cfg.input.dim cfg.input.output output ∧
        ∀ loc ∈ domain, ¬ InWords cfg.input.output (cfg.input.m*cfg.input.dim) loc → output loc = launch.initial loc) :=
  Scalar.triple_checked (correct cfg q key value scale domain hcover)
theorem checked_nonvacuous (cfg : Config) (q key value : Attention.Matrix) (scale : ℝ) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    Scalar.CheckedNonvacuous code (Pre cfg q key value scale) (fun _ => domain) :=
  Scalar.nonvacuous_checked_of_unique_sites checked_sites (nonvacuous cfg q key value scale domain hglobal)

end
end Ptx.ScalarAttentionEvent

namespace Ptx.AtomicDispatchEvent
open Ptx.ISA Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

theorem checked_sites : Scalar.uniqueBarrierSites code = true := by decide
theorem checked_correct (cfg : Config) (domain : List Location) (hcover : Covers cfg domain) :
    Scalar.CheckedTriple code (Pre cfg) (fun _ => domain) (fun launch output => Post cfg launch.initial output domain) :=
  Scalar.triple_checked (correct cfg domain hcover)
theorem checked_nonvacuous (cfg : Config) (domain : List Location)
    (hglobal : ∀ loc ∈ domain, loc.space = .global) :
    Scalar.CheckedNonvacuous code (Pre cfg) (fun _ => domain) :=
  Scalar.nonvacuous_checked_of_unique_sites checked_sites (nonvacuous cfg domain hglobal)

end
end Ptx.AtomicDispatchEvent

namespace Ptx.FloatLiteralsUniversal
open Ptx.ISA Ptx.Scalar Ptx.FloatLiteralsMemory
noncomputable section

theorem checked_sites : Scalar.uniqueBarrierSites FloatLiteralsTrace.code = true := by decide
theorem checked_correct (dst : Nat) :
    Scalar.CheckedTriple FloatLiteralsTrace.code (Pre dst) (fun _ => domain dst)
      (fun _ output => observedValue dst output = some 9) :=
  Scalar.triple_checked (correct dst)
theorem checked_nonvacuous (dst : Nat) :
    Scalar.CheckedNonvacuous FloatLiteralsTrace.code (Pre dst) (fun _ => domain dst) :=
  Scalar.nonvacuous_checked_of_unique_sites checked_sites (nonvacuous dst)

end
end Ptx.FloatLiteralsUniversal
