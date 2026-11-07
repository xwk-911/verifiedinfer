import Ptx.Kernels.HopperStageSchedules
import Ptx.Hopper.TmaPackedRows
import Ptx.ISA.TensorMapStorage

/-! Independent initial storage for the actual stage's two opaque tensor maps
and packed input matrices. Source payload agreement follows from the real TMA
address function, not an assumed post-transfer view. This is not yet RF,
resource/control, lifetime/allocation or global observer admission. -/
namespace Ptx.Kernels.HopperStage
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def representedInitial (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ)
    (frame : Location → Symbolic.Byte) (loc : Location) : Symbolic.Byte :=
  if loc.space = .global then
    if 4096 ≤ loc.address ∧ loc.address < 4224 then .tensorMapPart aView (loc.address-4096)
    else if 4224 ≤ loc.address ∧ loc.address < 4352 then .tensorMapPart bView (loc.address-4224)
    else if 65536 ≤ loc.address ∧ loc.address < 67584 then Wgmma.tileByte a b (loc.address-65536)
    else if 69632 ≤ loc.address ∧ loc.address < 69888 then Wgmma.tileByte a b (2048+(loc.address-69632))
    else frame loc
  else frame loc
def maps (address : Nat) : Option Tma.Descriptor2D :=
  if address = 4096 then some aView else if address = 4224 then some bView else none

theorem initial_descriptor_a (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame) :
    TensorMap.Stored (representedInitial a b frame) ⟨.global,4096⟩ aView := by
  intro offset ho
  have h : 4096 ≤ 4096+offset ∧ 4096+offset < 4224 := by omega
  simp only [representedInitial,Location.add,ite_true,if_pos h,Nat.add_sub_cancel_left]
theorem initial_descriptor_b (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame) :
    TensorMap.Stored (representedInitial a b frame) ⟨.global,4224⟩ bView := by
  intro offset ho
  have ha : ¬(4096 ≤ 4224+offset ∧ 4224+offset < 4224) := by omega
  have hb : 4224 ≤ 4224+offset ∧ 4224+offset < 4352 := by omega
  simp only [representedInitial,Location.add,ite_true,if_neg ha,if_pos hb,Nat.add_sub_cancel_left]
theorem initial_a_byte (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame) (offset : Fin 2048) :
    representedInitial a b frame ⟨.global,65536+offset.val⟩ =
      transferView a b ⟨.shared .zero,16+offset.val⟩ := by
  have ho := offset.isLt
  have hd : ¬(4096 ≤ 65536+offset.val ∧ 65536+offset.val < 4224) := by omega
  have he : ¬(4224 ≤ 65536+offset.val ∧ 65536+offset.val < 4352) := by omega
  have ha : 65536 ≤ 65536+offset.val ∧ 65536+offset.val < 67584 := by omega
  simp only [representedInitial,ite_true,if_neg hd,if_neg he,if_pos ha,
    transferView,Wgmma.tileMemory,Nat.add_sub_cancel_left]
theorem initial_b_byte (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame) (offset : Fin 256) :
    representedInitial a b frame ⟨.global,69632+offset.val⟩ =
      transferView a b ⟨.shared .zero,2064+offset.val⟩ := by
  have ho := offset.isLt
  have hd : ¬(4096 ≤ 69632+offset.val ∧ 69632+offset.val < 4224) := by omega
  have he : ¬(4224 ≤ 69632+offset.val ∧ 69632+offset.val < 4352) := by omega
  have ha : ¬(65536 ≤ 69632+offset.val ∧ 69632+offset.val < 67584) := by omega
  have hb : 69632 ≤ 69632+offset.val ∧ 69632+offset.val < 69888 := by omega
  have hs : 2064+offset.val-16 = 2048+offset.val := by omega
  simp only [representedInitial,ite_true,if_neg hd,if_neg he,if_neg ha,if_pos hb,
    transferView,Wgmma.tileMemory,Nat.add_sub_cancel_left,hs]
theorem initial_frame (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame) (loc)
    (ha : ¬(4096 ≤ loc.address ∧ loc.address < 4224))
    (hb : ¬(4224 ≤ loc.address ∧ loc.address < 4352))
    (hc : ¬(65536 ≤ loc.address ∧ loc.address < 67584))
    (hd : ¬(69632 ≤ loc.address ∧ loc.address < 69888)) :
    representedInitial a b frame loc = frame loc := by
  simp only [representedInitial,if_neg ha,if_neg hb,if_neg hc,if_neg hd,ite_self]

theorem all_source_copies {a b id op} (hc : Tma.copyAt (candidate a b).view id = some op) :
    op = copyA a ∨ op = copyB b := by
  have he := Unified.view_tma_iff.mp (Tma.copyAt_iff.mp hc)
  obtain ⟨actual,ht,_,hget⟩ := Unified.eventAt_trace he
  obtain ⟨lane,rfl⟩ := List.mem_ofFn.mp ht
  have hm := List.mem_of_getElem? hget
  change Wgmma.Event.base (.tmaIssue op) ∈ middleEvents a b lane (leader lane)++
    (nativeEvents a b lane (leader lane)++(storeResult a b lane (leader lane)).2) at hm
  rw [actual_store_events] at hm
  cases hl : leader lane <;> simp [middleEvents,nativeEvents,storedEvents,hl] at hm
  simpa only [copyA,copyB] using hm
theorem stage_descriptor_agreement (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    Tma.DescriptorAgreement (candidate a b).view maps := by
  intro id op hc
  rcases all_source_copies hc with rfl | rfl <;> simp [maps,copyA,copyB]
theorem stage_payload_agreement (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) (frame) :
    Tma.PayloadAgreement (candidate a b).view (representedInitial a b frame) := by
  intro id op hc offset ho
  rcases all_source_copies hc with rfl | rfl
  · have hb : offset < 2048 := ho
    have hp := transfer_a_payload a b ⟨offset,hb⟩
    rw [← initial_a_byte a b frame ⟨offset,hb⟩] at hp
    change (aPayload a)[offset]? = some (Tma.byteValue aView ⟨0,0⟩ _ offset)
    rw [Tma.copied_byte (d := aView) (Tma.packed_rows_source_byte 65536 8 offset (by omega))]
    exact hp
  · have hb : offset < 256 := ho
    have hp := transfer_b_payload a b ⟨offset,hb⟩
    rw [← initial_b_byte a b frame ⟨offset,hb⟩] at hp
    change (bPayload b)[offset]? = some (Tma.byteValue bView ⟨0,0⟩ _ offset)
    rw [Tma.copied_byte (d := bView) (Tma.packed_rows_source_byte 69632 1 offset (by omega))]
    exact hp
theorem wrong_initial_input_rejected (a : Wgmma.ACoord → ℝ) (b : Wgmma.BCoord → ℝ) :
    ¬Tma.PayloadAgreement (candidate a b).view (fun _ => .bits (byte 0)) := by
  intro h
  have hh := h (copyId 5) (copyA a) (actual_copy_a a b) 0 (by change 0 < 2048; decide)
  change (aPayload a)[0]? = some (Tma.byteValue aView ⟨0,0⟩ (fun _ => .bits (byte 0)) 0) at hh
  rw [Tma.copied_byte (d := aView) (Tma.packed_rows_source_byte 65536 8 0 (by decide))] at hh
  change some (Symbolic.Byte.realPart .f16 _ 0) = some (Symbolic.Byte.bits (byte 0)) at hh
  cases hh

end
end Ptx.Kernels.HopperStage
