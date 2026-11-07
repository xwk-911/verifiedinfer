import Ptx.Kernels.HopperDoubleBufferResourceUnique

/-! Thread-local program order is preserved by the constructed resource
histories. This is separate from exhaustion and combined control acyclicity. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

inductive HistorySource where
  | init
  | expect (phase : Nat)
  | wait (phase : Nat) (lane : Wgmma.Lane)
  | inval
  deriving DecidableEq

def sourceAllowed (tiles : Nat) (slot : Stage) : HistorySource → Prop
  | .expect phase | .wait phase _ => phase < uses tiles slot
  | _ => True
def historySourceId (a : TileA) (b : TileB) (tiles : Nat) (slot : Stage) : HistorySource → Ptx.Event.EventId
  | .init => dataInitId tiles slot
  | .expect phase => dataExpectId a b tiles (stageTile slot phase)
  | .wait phase lane => dataWaitId a b tiles (stageTile slot phase) lane
  | .inval => dataInvalId a b tiles slot
def historySourceLane : HistorySource → Nat
  | .wait _ lane => lane.val
  | _ => 0
def historySourceTile (slot : Stage) : HistorySource → Nat
  | .expect phase | .wait phase _ => stageTile slot phase
  | _ => 0
def historySourceSerial (tiles : Nat) (slot : Stage) : HistorySource → Nat
  | .init => slot.val
  | .expect phase => expectSerial (stageTile slot phase)
  | .wait phase lane => waitSerial (stageTile slot phase) lane
  | .inval => invalSerial tiles slot
def historySourcePosition (tiles : Nat) (slot : Stage) : HistorySource → Nat
  | .init => 0
  | .expect phase => phaseStart phase
  | .wait phase lane => phaseWaitIndex phase lane
  | .inval => phaseStart (uses tiles slot)

theorem source_allowed_tile_bound (tiles slot kind) (hk : sourceAllowed tiles slot kind) :
    (match kind with | .expect phase | .wait phase _ => stageTile slot phase < tiles | _ => True) := by
  cases kind with
  | init => trivial
  | inval => trivial
  | expect phase => exact (stage_tile_in_range tiles slot phase).mpr hk
  | wait phase lane => exact (stage_tile_in_range tiles slot phase).mpr hk

theorem history_source_lane_bound (kind) : historySourceLane kind < 128 := by
  cases kind <;> simp only [historySourceLane] <;> try decide
  exact Fin.isLt _

theorem history_source_serial_value (a b tiles slot kind) (hk : sourceAllowed tiles slot kind) :
    (historySourceId a b tiles slot kind).serial = historySourceSerial tiles slot kind := by
  cases kind with
  | init => rfl
  | inval => exact data_inval_serial a b tiles slot
  | expect phase => exact data_expect_serial a b tiles _ ((stage_tile_in_range tiles slot phase).mpr hk)
  | wait phase lane => exact data_wait_serial a b tiles _ lane ((stage_tile_in_range tiles slot phase).mpr hk)

theorem history_source_lane_value (a b tiles slot kind) :
    resourceLane (historySourceId a b tiles slot kind).thread = historySourceLane kind := by
  cases kind <;> exact resource_lane_value tiles _

theorem history_source_position_value (a b tiles slot kind) (hk : sourceAllowed tiles slot kind) :
    resourcePosition tiles slot (.source (historySourceId a b tiles slot kind)) = historySourcePosition tiles slot kind := by
  cases kind with
  | init => exact data_init_position tiles slot
  | inval => exact data_inval_position a b tiles slot
  | expect phase => exact data_expect_position a b tiles slot phase hk
  | wait phase lane => exact data_wait_position a b tiles slot phase lane hk

theorem history_serial_implies_position (tiles slot left right)
    (hl : sourceAllowed tiles slot left) (hr : sourceAllowed tiles slot right)
    (hlane : historySourceLane left = historySourceLane right)
    (hserial : historySourceSerial tiles slot left < historySourceSerial tiles slot right) :
    historySourcePosition tiles slot left < historySourcePosition tiles slot right := by
  have hltile := source_allowed_tile_bound tiles slot left hl
  have hrtile := source_allowed_tile_bound tiles slot right hr
  have hllane := history_source_lane_bound left
  have hrlane := history_source_lane_bound right
  have hs := slot.isLt
  by_cases hzl : historySourceTile slot left = 0 <;>
    by_cases hzr : historySourceTile slot right = 0 <;>
    by_cases hll : historySourceLane left = 0 <;>
    by_cases hrr : historySourceLane right = 0 <;>
    cases left <;> cases right <;>
    simp only [historySourceLane,historySourceTile,historySourceSerial,historySourcePosition,
      stageTile,expectSerial,waitSerial,HopperStage.leader,decide_eq_true_eq,invalSerial,phaseStart,phaseWaitIndex,uses] at * <;>
    (try simp only [hzl,hzr,hll,hrr,ite_true,ite_false] at hserial) <;> first | contradiction | omega

theorem history_source_member_cases (a b tiles slot) (entry : Tma.Entry) (he : entry ∈ dataResourceHistory a b tiles slot)
    (event : Ptx.Event.EventId) (ho : entry.origin = .source event) :
    ∃ kind, sourceAllowed tiles slot kind ∧ event = historySourceId a b tiles slot kind := by
  simp only [dataResourceHistory,List.mem_append,List.mem_singleton] at he
  rcases he with (rfl | he) | rfl
  · exact ⟨.init,trivial,(Tma.Origin.source.inj ho).symm⟩
  · obtain ⟨phase,hp,he⟩ := (data_phases_entry a b tiles slot _ entry).mp he
    simp only [dataPhaseEntries,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with (rfl | rfl | rfl) | he
    · exact ⟨.expect phase,hp,(Tma.Origin.source.inj ho).symm⟩
    · cases ho
    · cases ho
    · obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp he
      exact ⟨.wait phase lane,hp,(Tma.Origin.source.inj ho).symm⟩
  · exact ⟨.inval,trivial,(Tma.Origin.source.inj ho).symm⟩

theorem data_history_index_is_position (a b tiles slot) (entry : Tma.Entry) (he : entry ∈ dataResourceHistory a b tiles slot) :
    ((dataResourceHistory a b tiles slot).map Tma.Entry.origin).idxOf entry.origin = resourcePosition tiles slot entry.origin := by
  obtain ⟨index,hi⟩ := List.mem_iff_getElem?.mp he
  rw [data_history_origin_index a b tiles slot index entry hi,data_history_recovered_index a b tiles slot index entry hi]

theorem data_history_source_order (a b tiles slot) : Tma.SourceOrder (dataResourceHistory a b tiles slot) := by
  intro first hf last hl hbefore
  cases hoFirst : first.origin with
  | notification copy => simp [Tma.SourceBefore,hoFirst] at hbefore
  | source firstId =>
    cases hoLast : last.origin with
    | notification copy => simp [Tma.SourceBefore,hoFirst,hoLast] at hbefore
    | source lastId =>
      obtain ⟨fk,hfk,hfirst⟩ := history_source_member_cases a b tiles slot first hf firstId hoFirst
      obtain ⟨lk,hlk,hlast⟩ := history_source_member_cases a b tiles slot last hl lastId hoLast
      simp only [Tma.SourceBefore,hoFirst,hoLast] at hbefore
      have hlanes := congrArg resourceLane hbefore.1
      rw [hfirst,hlast,history_source_lane_value,history_source_lane_value] at hlanes
      have hserial := hbefore.2
      rw [hfirst,hlast,history_source_serial_value a b tiles slot fk hfk,history_source_serial_value a b tiles slot lk hlk] at hserial
      have hfi := data_history_index_is_position a b tiles slot first hf
      have hli := data_history_index_is_position a b tiles slot last hl
      rw [hoFirst] at hfi
      rw [hoLast] at hli
      rw [hfi,hli,hfirst,hlast,history_source_position_value a b tiles slot fk hfk,history_source_position_value a b tiles slot lk hlk]
      exact history_serial_implies_position tiles slot fk lk hfk hlk hlanes hserial

theorem data_notification_a_before_wait (a b tiles slot phase lane) (hp : phase < uses tiles slot) :
    Tma.Before (dataResourceHistory a b tiles slot)
      (.notification (dataCopyAId a b tiles (stageTile slot phase)))
      (.source (dataWaitId a b tiles (stageTile slot phase) lane)) :=
  Tma.observation_before_of_unique (data_history_origins_unique a b tiles slot) (data_observe_a a b tiles slot phase hp lane)

theorem data_notification_b_before_wait (a b tiles slot phase lane) (hp : phase < uses tiles slot) :
    Tma.Before (dataResourceHistory a b tiles slot)
      (.notification (dataCopyBId a b tiles (stageTile slot phase)))
      (.source (dataWaitId a b tiles (stageTile slot phase) lane)) :=
  Tma.observation_before_of_unique (data_history_origins_unique a b tiles slot) (data_observe_b a b tiles slot phase hp lane)

end
end Ptx.Kernels.HopperDoubleBuffer
