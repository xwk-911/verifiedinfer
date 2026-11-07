import Ptx.Kernels.HopperDoubleBufferResourceRanks

/-! Recoverable positions enumerate every history index exactly once. This
proves origin uniqueness, not exhaustion of the candidate's resource inventory. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem ofFn_add_range (start n : Nat) :
    List.ofFn (fun i : Fin n => start+i.val) = List.range' start n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ,List.range']
    have he : (fun i : Fin n => start+i.succ.val) = (fun i : Fin n => start+1+i.val) := by
      funext i
      simp only [Fin.val_succ]
      omega
    rw [he,ih]
    simp only [Fin.val_zero,Nat.add_zero]

theorem data_phase_positions (a b tiles slot phase) (hp : phase < uses tiles slot) :
    (dataPhaseEntries a b tiles slot phase).map (fun entry => resourcePosition tiles slot entry.origin) =
      List.range' (phaseStart phase) 131 := by
  simp only [dataPhaseEntries,List.map_append,List.map_cons,List.map_nil,
    data_expect_position a b tiles slot phase hp,data_copy_a_position a b tiles slot phase hp,
    data_copy_b_position a b tiles slot phase hp,List.map_ofFn,Function.comp_def,data_wait_position a b tiles slot phase _ hp,
    phaseWaitIndex,noticeAIndex,noticeBIndex]
  rw [ofFn_add_range]
  have hthree : List.range' (phaseStart phase) 3 =
      [phaseStart phase,phaseStart phase+1,phaseStart phase+2] := by
    simp [List.range',Nat.add_assoc]
  have he := List.range'_append_1 (s := phaseStart phase) (m := 3) (n := 128)
  rw [hthree] at he
  exact he

theorem data_phases_positions (a b tiles slot n) (hn : n ≤ uses tiles slot) :
    (dataPhases a b tiles slot n).map (fun entry => resourcePosition tiles slot entry.origin) = List.range' 1 (131*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dataPhases,List.map_append,ih (by omega),data_phase_positions a b tiles slot n (by omega),phaseStart,
      List.range'_append_1]
    congr 1

theorem data_history_positions (a b tiles slot) :
    (dataResourceHistory a b tiles slot).map (fun entry => resourcePosition tiles slot entry.origin) =
      List.range (2+131*uses tiles slot) := by
  simp only [dataResourceHistory,List.map_append,List.map_cons,List.map_nil,data_init_position,
    data_inval_position,data_phases_positions a b tiles slot _ (Nat.le_refl _)]
  have hf : [0] = List.range' 0 1 := rfl
  have hl : [phaseStart (uses tiles slot)] = List.range' (1+131*uses tiles slot) 1 := rfl
  rw [hf,List.range'_append_1,hl]
  have happ := List.range'_append_1 (s := 0) (m := 1+131*uses tiles slot) (n := 1)
  simp only [Nat.zero_add] at happ
  rw [happ,List.range_eq_range']
  congr 1
  omega

theorem data_history_origins_unique (a b tiles slot) :
    ((dataResourceHistory a b tiles slot).map Tma.Entry.origin).Nodup := by
  apply List.Nodup.of_map (resourcePosition tiles slot)
  rw [List.map_map]
  change ((dataResourceHistory a b tiles slot).map (fun entry => resourcePosition tiles slot entry.origin)).Nodup
  rw [data_history_positions]
  exact List.nodup_range

theorem data_history_origin_index (a b tiles slot) (index : Nat) (entry : Tma.Entry)
    (he : (dataResourceHistory a b tiles slot)[index]? = some entry) :
    ((dataResourceHistory a b tiles slot).map Tma.Entry.origin).idxOf entry.origin = index :=
  Tma.origin_index (data_history_origins_unique a b tiles slot) he

theorem data_history_recovered_index (a b tiles slot) (index : Nat) (entry : Tma.Entry)
    (he : (dataResourceHistory a b tiles slot)[index]? = some entry) :
    resourcePosition tiles slot entry.origin = index := by
  have hm : ((dataResourceHistory a b tiles slot).map (fun entry => resourcePosition tiles slot entry.origin))[index]? =
      some (resourcePosition tiles slot entry.origin) := by simp only [List.getElem?_map,he,Option.map_some]
  rw [data_history_positions] at hm
  have hi := (List.getElem?_eq_some_iff.mp he).1
  rw [data_history_length] at hi
  simpa only [List.getElem?_range,hi,dite_true,Option.some.injEq] using hm.symm

end
end Ptx.Kernels.HopperDoubleBuffer
