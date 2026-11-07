import Ptx.Kernels.AmpereTiledBounds

/-! Full PC-zero local source instances. The active oracle deliberately lacks
memory-value agreement; these are not complete checked launch witnesses. -/
namespace Ptx.AmpereTiledSourceTests
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec
noncomputable section

def cfg : Config := ⟨32,16,48,128,8192,16384,18436⟩
def id : ThreadId := ⟨⟨1,1,0⟩,⟨3,7,0⟩⟩
def ctx (input : Config) (thread : ThreadId) : Scalar.Context :=
  {params := params input,id := thread,block := (geometry input).block}
def oracle : Oracle := {
  scalar := fun _ => .integer 0
  bytes := fun q => List.replicate 8 (.bits (byte q))
  word32 := fun _ => .packed ⟨1,1⟩
  matrix := fun _ _ => 42
}
def hostileOracle : Oracle := {
  scalar := fun _ => .integer 99
  bytes := fun _ => []
  word32 := fun _ => .integer 123
  matrix := fun _ _ => -999
}

theorem layout : Layout cfg := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · intro _; decide
  · intro _ _; norm_num [AmpereTiledSpec.Disjoint,cfg]
theorem valid : id.Valid (geometry cfg) := by simp [ThreadId.Valid,Dim3.Within,geometry,cfg,id]

def replies : AmpereTiledLoop.Replies (AmpereTiledEntry.loopConfig cfg (ctx cfg id)) oracle := {
  payload := fun step i => oracle.bytes (10*step+i.val)
  a := fun _ _ => ⟨1,1⟩
  b := fun _ _ => ⟨1,1⟩
  size := by intro step _ i; simp [oracle]
  bytes := by intro step _ i; simp [AmpereTiledEntry.loopConfig]
  wordA := by intro step _ i; rfl
  wordB := by intro step _ i; rfl
}

theorem complete_three_iterations :
    ∃ last emitted, Ampere.run (ctx cfg id) oracle AmpereTiledSource.code 127 {} = .ok (last,emitted) ∧
      last.scalar.core.thread.status = .done ∧ emitted.length = 55 ∧ last.scalar.core.queries = 30 :=
  AmpereTiledSource.active_run layout _ _ (AmpereTiledInit.canonical_params cfg) valid (by constructor <;> decide) replies

theorem source_a_pointer : AmpereTiledAddresses.a cfg (ctx cfg id) = 2360 := by rfl
theorem source_ah_pointer : AmpereTiledAddresses.ah cfg (ctx cfg id) = 3128 := by rfl
theorem source_b_pointer : AmpereTiledAddresses.b cfg (ctx cfg id) = 9656 := by rfl
theorem source_c_pointer : AmpereTiledAddresses.c cfg (ctx cfg id) = 17912 := by rfl
theorem source_ch_pointer : AmpereTiledAddresses.ch cfg (ctx cfg id) = 18424 := by rfl
theorem source_shared_pointers : AmpereTiledAddresses.sa (ctx cfg id) = 248 ∧
    AmpereTiledAddresses.sah (ctx cfg id) = 504 ∧ AmpereTiledAddresses.sb (ctx cfg id) = 760 ∧
    AmpereTiledAddresses.la (ctx cfg id) = 236 ∧ AmpereTiledAddresses.lb (ctx cfg id) = 748 := by decide

theorem last_a_copy_all_bytes : AmpereTiledBounds.copyStart cfg (ctx cfg id) 2 1+8 = cfg.a+2*(cfg.m*cfg.k) := by rfl
theorem last_b_copy_all_bytes : AmpereTiledBounds.copyStart cfg (ctx cfg id) 2 2+8 = cfg.b+2*(cfg.n*cfg.k) := by rfl
theorem last_copies_bounded (part : Fin 3) : AmpereTiledBounds.copyStart cfg (ctx cfg id) 2 part+8 ≤ cfg.arenaBytes :=
  AmpereTiledBounds.copy_span layout valid (by constructor <;> decide) (by decide) part

def zeroK : Config := ⟨16,8,0,4,4,4,520⟩
def zeroId : ThreadId := ⟨⟨0,0,0⟩,⟨3,7,0⟩⟩
theorem zero_k_layout : Layout zeroK := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · intro _; decide
  · intro _ hk; change (0 : Nat) < 0 at hk; omega
theorem zero_k_unaligned_input_alias : zeroK.a = zeroK.b ∧ zeroK.b = zeroK.c ∧ zeroK.a%8 = 4 := by decide
theorem zero_valid : zeroId.Valid (geometry zeroK) := by simp [ThreadId.Valid,Dim3.Within,geometry,zeroK,zeroId]
theorem zero_active : Active zeroK := ⟨by decide,by decide⟩
theorem zero_k_arbitrary_oracle (anyOracle : Oracle) :
    Ampere.run (ctx zeroK zeroId) anyOracle AmpereTiledSource.code 64 {} =
      .ok (AmpereTiledFinish.finalState (AmpereTiledGuard.exitState (AmpereTiledEntry.ready zeroK (ctx zeroK zeroId))),
        AmpereTiledFinish.events 252 508 (fun _ => 0)) :=
  AmpereTiledSource.zero_k_events zero_k_layout _ _ (AmpereTiledInit.canonical_params zeroK) zero_valid zero_active rfl
theorem zero_k_rejects_premature_completion {last emitted}
    (hr : Ampere.run (ctx zeroK zeroId) hostileOracle AmpereTiledSource.code 63 {} = .ok (last,emitted)) :
    last.scalar.core.thread.status ≠ .done := by
  intro hd
  have hc := AmpereTiledSource.zero_k_complete_counts zero_k_layout _ _
    (AmpereTiledInit.canonical_params zeroK) zero_valid zero_active rfl hr hd
  omega

def rowMasked : Config := ⟨0,4294967288,4294967280,2^64-1,2^64-1,2^64-1,0⟩
def farId : ThreadId := ⟨⟨536870910,0,0⟩,⟨3,7,0⟩⟩
theorem masked_layout : Layout rowMasked := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · intro ha; have hh := ha.1; change (0 : Nat) < 0 at hh; omega
  · intro ha _; have hh := ha.1; change (0 : Nat) < 0 at hh; omega
theorem masked_valid : farId.Valid (geometry rowMasked) := by simp [ThreadId.Valid,Dim3.Within,geometry,rowMasked,farId]
theorem masked_large_cta_index : AmpereTiledInit.tileCol (ctx rowMasked farId) = 4294967280 := by rfl
theorem row_masked_arbitrary_oracle (anyOracle : Oracle) :
    Ampere.run (ctx rowMasked farId) anyOracle AmpereTiledSource.code 15 {} =
      .ok (AmpereTiledInit.maskedFinal rowMasked (ctx rowMasked farId),[]) :=
  AmpereTiledSource.row_masked_run _ _ (AmpereTiledInit.canonical_params rowMasked) rfl

def colMasked : Config := ⟨16,0,48,2^64-1,2^64-1,2^64-1,0⟩
theorem col_masked_layout : Layout colMasked := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · intro ha; have hh := ha.2; change (0 : Nat) < 0 at hh; omega
  · intro ha _; have hh := ha.2; change (0 : Nat) < 0 at hh; omega
theorem col_masked_arbitrary_oracle (anyOracle : Oracle) :
    Ampere.run (ctx colMasked zeroId) anyOracle AmpereTiledSource.code 17 {} =
      .ok (AmpereTiledInit.maskedFinal colMasked (ctx colMasked zeroId),[]) :=
  AmpereTiledSource.col_masked_run col_masked_layout _ _ (AmpereTiledInit.canonical_params colMasked)
    (by simp [ctx,ThreadId.Valid,Dim3.Within,geometry,colMasked,zeroId]) (by decide) rfl

end
end Ptx.AmpereTiledSourceTests
