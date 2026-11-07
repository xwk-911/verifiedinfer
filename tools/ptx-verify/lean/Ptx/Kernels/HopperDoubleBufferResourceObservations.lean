import Ptx.Kernels.HopperDoubleBufferResourcePrefixes

/-! Actual transfer-to-wait phase observations in the constructed histories.
These checked observations do not replace HistoryValid, causal ordering,
shared-byte visibility or allocation/in-flight lifetime admission. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def isInitialization (entry : Tma.Entry) : Bool := match entry.operation with | .init _ => true | _ => false
def awaitingTransfer (phase : Nat) (bytes : Int) : Mbarrier.PhaseState := ⟨phase,1,0,bytes,true⟩

theorem data_phase_no_initialization (a b tiles slot phase) :
    (dataPhaseEntries a b tiles slot phase).filter isInitialization = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro entry he
  simp only [dataPhaseEntries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with (rfl | rfl | rfl) | he
  · simp [isInitialization]
  · simp [isInitialization]
  · simp [isInitialization]
  · obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp he
    simp [isInitialization]

theorem data_phases_no_initialization (a b tiles slot n) :
    (dataPhases a b tiles slot n).filter isInitialization = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dataPhases,List.filter_append,ih,data_phase_no_initialization]; rfl

theorem data_phase_take_no_initialization (a b tiles slot phase index) :
    ((dataPhaseEntries a b tiles slot phase).take index).filter isInitialization = [] := by
  have hh := List.filter_eq_nil_iff.mp (data_phase_no_initialization a b tiles slot phase)
  exact List.filter_eq_nil_iff.mpr (fun entry he => hh entry (List.mem_of_mem_take he))

theorem data_phase_lifetime (a b tiles slot phase) (hp : phase < uses tiles slot) (index : Nat) (hi : index ≤ 131) :
    Tma.lifetimeBefore (dataResourceHistory a b tiles slot) (phaseStart phase+index) = 1 := by
  change (((dataResourceHistory a b tiles slot).take (phaseStart phase+index)).filter isInitialization).length = 1
  rw [data_history_take a b tiles slot phase hp index hi,List.filter_append,List.filter_append,
    data_phases_no_initialization,data_phase_take_no_initialization]
  rfl

theorem data_notice_a_prefix (a b tiles slot phase) (hp : phase < uses tiles slot) :
    Mbarrier.run none (((dataResourceHistory a b tiles slot).map Tma.Entry.operation).take (noticeAIndex phase)) =
      some (some (awaitingTransfer phase 2304)) := by
  rw [← List.map_take,noticeAIndex,data_history_take a b tiles slot phase hp 1 (by decide),List.map_append,
    Mbarrier.run_append,data_history_prefix_run,Option.bind_some]
  change Mbarrier.run (some (readyState phase)) [.arriveExpectTx 2304] = _
  simp [Mbarrier.run,Mbarrier.step,Mbarrier.accept,Mbarrier.WellFormed,Mbarrier.finish,Mbarrier.limit,readyState,awaitingTransfer]

theorem data_notice_b_prefix (a b tiles slot phase) (hp : phase < uses tiles slot) :
    Mbarrier.run none (((dataResourceHistory a b tiles slot).map Tma.Entry.operation).take (noticeBIndex phase)) =
      some (some (awaitingTransfer phase 256)) := by
  rw [← List.map_take,noticeBIndex,data_history_take a b tiles slot phase hp 2 (by decide),List.map_append,
    Mbarrier.run_append,data_history_prefix_run,Option.bind_some]
  change Mbarrier.run (some (readyState phase)) [.arriveExpectTx 2304,.completeTx 2048] = _
  simp [Mbarrier.run,Mbarrier.step,Mbarrier.accept,Mbarrier.WellFormed,Mbarrier.finish,Mbarrier.limit,readyState,awaitingTransfer]

theorem data_notice_a_stamp (a b tiles slot phase) (hp : phase < uses tiles slot) :
    Tma.stampBefore (dataResourceHistory a b tiles slot) (noticeAIndex phase) = some ⟨1,phase⟩ := by
  rw [Tma.stampBefore,data_notice_a_prefix a b tiles slot phase hp]
  simp only [noticeAIndex,data_phase_lifetime a b tiles slot phase hp 1 (by decide),awaitingTransfer]

theorem data_notice_b_stamp (a b tiles slot phase) (hp : phase < uses tiles slot) :
    Tma.stampBefore (dataResourceHistory a b tiles slot) (noticeBIndex phase) = some ⟨1,phase⟩ := by
  rw [Tma.stampBefore,data_notice_b_prefix a b tiles slot phase hp]
  simp only [noticeBIndex,data_phase_lifetime a b tiles slot phase hp 2 (by decide),awaitingTransfer]

theorem data_wait_stamp (a b tiles slot phase) (hp : phase < uses tiles slot) (lane : Wgmma.Lane) :
    Tma.stampBefore (dataResourceHistory a b tiles slot) (phaseWaitIndex phase lane) = some ⟨1,phase+1⟩ := by
  rw [Tma.stampBefore,data_history_wait_prefix a b tiles slot phase hp lane]
  have hl : Tma.lifetimeBefore (dataResourceHistory a b tiles slot) (phaseWaitIndex phase lane) = 1 := by
    rw [phaseWaitIndex,Nat.add_assoc]
    exact data_phase_lifetime a b tiles slot phase hp (3+lane.val) (by have := lane.isLt; omega)
  rw [hl]
  by_cases hz : lane.val = 0 <;> simp [hz,transferredState,readyState]

theorem data_observe_a (a b tiles slot phase) (hp : phase < uses tiles slot) (lane : Wgmma.Lane) :
    Tma.observation (dataResourceHistory a b tiles slot) (noticeAIndex phase) (phaseWaitIndex phase lane) =
      some (dataCopyAId a b tiles (stageTile slot phase),dataWaitId a b tiles (stageTile slot phase) lane) := by
  rw [Tma.observation,data_history_notice_a_at a b tiles slot phase hp,data_history_wait_at a b tiles slot phase hp lane]
  simp only [bind,Option.bind,Tma.noticeCopy,Tma.waitEvent]
  rw [data_notice_a_stamp a b tiles slot phase hp,data_wait_stamp a b tiles slot phase hp lane]
  dsimp only
  rw [ite_eq_left (by simp [noticeAIndex,phaseWaitIndex]; omega)]

theorem data_observe_b (a b tiles slot phase) (hp : phase < uses tiles slot) (lane : Wgmma.Lane) :
    Tma.observation (dataResourceHistory a b tiles slot) (noticeBIndex phase) (phaseWaitIndex phase lane) =
      some (dataCopyBId a b tiles (stageTile slot phase),dataWaitId a b tiles (stageTile slot phase) lane) := by
  rw [Tma.observation,data_history_notice_b_at a b tiles slot phase hp,data_history_wait_at a b tiles slot phase hp lane]
  simp only [bind,Option.bind,Tma.noticeCopy,Tma.waitEvent]
  rw [data_notice_b_stamp a b tiles slot phase hp,data_wait_stamp a b tiles slot phase hp lane]
  dsimp only
  rw [ite_eq_left (by simp [noticeBIndex,phaseWaitIndex]; omega)]

theorem data_old_phase_not_observed (a b tiles slot) (old current : Nat)
    (ho : old < uses tiles slot) (hc : current < uses tiles slot) (hne : old ≠ current) (lane : Wgmma.Lane) :
    Tma.observation (dataResourceHistory a b tiles slot) (noticeAIndex old) (phaseWaitIndex current lane) = none := by
  rw [Tma.observation,data_history_notice_a_at a b tiles slot old ho,data_history_wait_at a b tiles slot current hc lane]
  simp only [bind,Option.bind,Tma.noticeCopy,Tma.waitEvent]
  rw [data_notice_a_stamp a b tiles slot old ho,data_wait_stamp a b tiles slot current hc lane]
  dsimp only
  rw [ite_eq_right (by simp; omega)]

theorem data_old_b_phase_not_observed (a b tiles slot) (old current : Nat)
    (ho : old < uses tiles slot) (hc : current < uses tiles slot) (hne : old ≠ current) (lane : Wgmma.Lane) :
    Tma.observation (dataResourceHistory a b tiles slot) (noticeBIndex old) (phaseWaitIndex current lane) = none := by
  rw [Tma.observation,data_history_notice_b_at a b tiles slot old ho,data_history_wait_at a b tiles slot current hc lane]
  simp only [bind,Option.bind,Tma.noticeCopy,Tma.waitEvent]
  rw [data_notice_b_stamp a b tiles slot old ho,data_wait_stamp a b tiles slot current hc lane]
  dsimp only
  rw [ite_eq_right (by simp; omega)]

end
end Ptx.Kernels.HopperDoubleBuffer
