import Ptx.Kernels.AtomicDispatchEvents
import Ptx.Event.AtomicRules

/-! Access layout, mixed-size exclusion and counter eligibility, all derived
from source events and separated four-byte cells. Output races are not assumed
away before ticket uniqueness has been proved. -/
namespace Ptx.AtomicDispatchEvent
open Ptx.ISA Ptx.Event Ptx.Scalar Ptx.AtomicDispatchTrace
noncomputable section

def Cell (cfg : Config) (base : Location) : Prop := base = counterLoc cfg ∨ base = xLoc cfg ∨ base = yLoc cfg

theorem event_footprint (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    {e : EventId} (he : execution.Present e) :
    ∃ base, Cell cfg base ∧ (execution.eventAt e).bind Kind.footprint = some (base,4) := by
  cases hkind : execution.eventAt e with
  | none => simp [Candidate.Present,hkind] at he
  | some kind =>
    obtain ⟨value,_,hs⟩ := event_shape cfg hw hd hg hp hkind
    rcases hs with ⟨_,rfl⟩ | ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩
    · exact ⟨counterLoc cfg,Or.inl rfl,by simp [Kind.footprint,atomicAddBytes]⟩
    · exact ⟨xLoc cfg,Or.inr (Or.inl rfl),by simp [Kind.footprint,u32Bytes]⟩
    · exact ⟨yLoc cfg,Or.inr (Or.inr rfl),by simp [Kind.footprint,u32Bytes]⟩

theorem cell_global {cfg : Config} {base : Location} (hc : Cell cfg base) : base.space = .global := by
  rcases hc with rfl | rfl | rfl <;> rfl

theorem cells_overlap_equal (cfg : Config) {a b loc : Location}
    (ha : Cell cfg a) (hb : Cell cfg b)
    (hla : a.address ≤ loc.address) (hua : loc.address < a.address+4)
    (hlb : b.address ≤ loc.address) (hub : loc.address < b.address+4) : a = b := by
  have region : ∀ c : Location, c.space = .global → c.address ≤ loc.address → loc.address < c.address+4 →
      InWords c.address 1 ⟨.global,loc.address⟩ := by intro c _ hlo hhi; exact ⟨rfl,hlo,by simpa using hhi⟩
  have hra := region a (cell_global ha) hla hua
  have hrb := region b (cell_global hb) hlb hub
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rfl
  · exact (words_disjoint cfg.counterX hra hrb).elim
  · exact (words_disjoint cfg.counterY hra hrb).elim
  · exact (words_disjoint cfg.counterX hrb hra).elim
  · rfl
  · exact (words_disjoint cfg.xy hra hrb).elim
  · exact (words_disjoint cfg.counterY hrb hra).elim
  · exact (words_disjoint cfg.xy hrb hra).elim
  · rfl

theorem overlap_same_footprint (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    {a b : EventId} (ho : execution.Overlap a b) : execution.SameFootprint a b := by
  obtain ⟨loc,ha,hb⟩ := ho
  obtain ⟨baseA,hca,hfa⟩ := event_footprint cfg hw hd hg hp (accesses_present ha)
  obtain ⟨baseB,hcb,hfb⟩ := event_footprint cfg hw hd hg hp (accesses_present hb)
  have hba := access_footprint_bounds ha hfa
  have hbb := access_footprint_bounds hb hfb
  have he := cells_overlap_equal cfg hca hcb hba.2.1 hba.2.2 hbb.2.1 hbb.2.2
  subst baseB
  exact ⟨(baseA,4),hfa,hfb⟩

theorem no_mixed (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params) (rf : ReadsFrom) :
    ¬ MixedSizeRace execution rf := by
  rintro ⟨a,b,hr,hn⟩
  exact hn (overlap_same_footprint cfg hw hd hg hp hr.overlap)

theorem footprint_counter_is_rmw (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    {e : EventId} (hf : (execution.eventAt e).bind Kind.footprint = some (counterLoc cfg,4)) :
    ∃ value, e.serial = 0 ∧ execution.eventAt e = some (.rmw .gpu (counterLoc cfg) (atomicAddBytes value 1)) := by
  cases he : execution.eventAt e with
  | none => simp [he] at hf
  | some kind =>
    obtain ⟨value,_,hs⟩ := event_shape cfg hw hd hg hp he
    rcases hs with ⟨hserial,rfl⟩ | ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩
    · exact ⟨value,hserial,rfl⟩
    · have heq : xLoc cfg = counterLoc cfg := by simpa [he,Kind.footprint,u32Bytes] using congrArg (fun x => x.map Prod.fst) hf
      have hword : InWords cfg.counter 1 (counterLoc cfg) := ⟨rfl,Nat.le_refl _,by simp [counterLoc]⟩
      have hother : InWords cfg.x 1 (counterLoc cfg) := by rw [← heq]; exact ⟨rfl,Nat.le_refl _,by simp [xLoc]⟩
      exact (words_disjoint cfg.counterX hword hother).elim
    · have heq : yLoc cfg = counterLoc cfg := by simpa [he,Kind.footprint,u32Bytes] using congrArg (fun x => x.map Prod.fst) hf
      have hword : InWords cfg.counter 1 (counterLoc cfg) := ⟨rfl,Nat.le_refl _,by simp [counterLoc]⟩
      have hother : InWords cfg.y 1 (counterLoc cfg) := by rw [← heq]; exact ⟨rfl,Nat.le_refl _,by simp [yLoc]⟩
      exact (words_disjoint cfg.counterY hword hother).elim

theorem counter_access (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    {e : EventId} {loc : Location} (hl : InWords cfg.counter 1 loc) (ha : execution.Accesses e loc) :
    ∃ value, e.serial = 0 ∧ execution.eventAt e = some (.rmw .gpu (counterLoc cfg) (atomicAddBytes value 1)) := by
  obtain ⟨base,hcell,hf⟩ := event_footprint cfg hw hd hg hp (accesses_present ha)
  have hb := access_footprint_bounds ha hf
  have he : base = counterLoc cfg := cells_overlap_equal cfg hcell (Or.inl rfl) hb.2.1 hb.2.2 hl.2.1
    (by simpa only [InWords, counterLoc,Nat.mul_one] using hl.2.2)
  subst base
  exact footprint_counter_is_rmw cfg hw hd hg hp hf

theorem counter_no_race (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    (rf : ReadsFrom) {a b : EventId} {loc : Location} (hl : InWords cfg.counter 1 loc)
    (ha : execution.Accesses a loc) (hb : execution.Accesses b loc) : ¬ DataRace execution rf a b := by
  obtain ⟨va,_,hea⟩ := counter_access cfg hw hd hg hp hl ha
  obtain ⟨vb,_,heb⟩ := counter_access cfg hw hd hg hp hl hb
  intro hr
  exact hr.notStrong (rmw_morally_strong hea heb (by simp [atomicAddBytes]) True.intro True.intro)

theorem counter_eligible (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    (rf : ReadsFrom) {read : EventId} {loc : Location} (hl : InWords cfg.counter 1 loc)
    (hr : execution.Accesses read loc) : Eligible execution rf read loc := by
  refine ⟨no_mixed cfg hw hd hg hp rf,?_⟩
  rintro (⟨writer,hwri,hrace⟩ | ⟨a,b,hwa,hwb,hrace⟩)
  · exact counter_no_race cfg hw hd hg hp rf hl hr (Or.inr hwri) hrace
  · exact counter_no_race cfg hw hd hg hp rf hl (Or.inr hwa) (Or.inr hwb) hrace

def counterId (cta : Nat) : EventId := ⟨id cta,0⟩

theorem counter_write_ids (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    {writer : EventId} {loc : Location} {value : Symbolic.Byte} (hl : InWords cfg.counter 1 loc)
    (hwrite : execution.writeByte writer loc = some value) : writer = counterId 0 ∨ writer = counterId 1 := by
  have ha : execution.Accesses writer loc := Or.inr (by rw [hwrite]; rfl)
  obtain ⟨v,hserial,he⟩ := counter_access cfg hw hd hg hp hl ha
  have hv := (event_shape cfg hw hd hg hp he).choose_spec.1
  obtain ⟨cta,hcta,hid⟩ := valid_id hv
  have hc : cta = 0 ∨ cta = 1 := by omega
  have hwid : writer = counterId cta := by cases writer; simp_all [counterId]
  rcases hc with rfl | rfl
  · exact Or.inl hwid
  · exact Or.inr hwid

theorem counter_offset (cfg : Config) {offset : Nat} (ho : offset < 4) :
    InWords cfg.counter 1 ((counterLoc cfg).add offset) := by
  exact ⟨rfl,by simp [counterLoc,Location.add],by simp only [counterLoc,Location.add,Nat.mul_one]; omega⟩

theorem access_bounds (cfg : Config) {launch : Scalar.Launch} {execution : Scalar.Candidate}
    (hw : Scalar.WellFormed code launch execution) (hd : execution.Complete)
    (hg : launch.geometry = geometry) (hp : Params cfg.counter cfg.x cfg.y launch.params)
    {event : EventId} (he : execution.Present event) :
    ∃ base, (execution.eventAt event).bind Kind.footprint = some (base,4) ∧
      base.space = .global ∧ base.address % 4 = 0 ∧ base.address+4 ≤ 2^64 := by
  obtain ⟨base,hcell,hf⟩ := event_footprint cfg hw hd hg hp he
  refine ⟨base,hf,cell_global hcell,?_⟩
  rcases hcell with rfl | rfl | rfl
  · exact ⟨cfg.counterAligned,cfg.counterEnd⟩
  · exact ⟨cfg.xAligned,cfg.xEnd⟩
  · exact ⟨cfg.yAligned,cfg.yEnd⟩

end
end Ptx.AtomicDispatchEvent
