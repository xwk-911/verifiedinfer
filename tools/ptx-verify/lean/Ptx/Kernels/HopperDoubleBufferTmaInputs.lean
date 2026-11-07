import Ptx.Kernels.HopperDoubleBufferTmaSources
import Ptx.ISA.TensorMapStorage

/-! Independently represented global input tiles and tensor maps. Actual
source-indexed copies have matching descriptors, source addresses and bytes.
These facts do not select RF/co edges or establish completion/publication. -/
namespace Ptx.Kernels.HopperDoubleBuffer
open Ptx.ISA Ptx.Hopper
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem packed_slice_source_byte (base height rows start offset : Nat)
    (ho : offset < 256*rows) (hs : start+rows ≤ height) :
    Tma.sourceByte ⟨base,128,height,256,128,rows,2⟩ ⟨0,start⟩ offset =
      some ⟨.global,base+256*start+offset⟩ := by
  have hx : offset/2%128 < 128 := Nat.mod_lt _ (by decide)
  have hy : offset/2/128 < rows := by omega
  have hb : Tma.InBounds ⟨base,128,height,256,128,rows,2⟩ ⟨0,start⟩ offset := by
    dsimp [Tma.InBounds,Tma.xAt,Tma.yAt]
    omega
  rw [Tma.sourceByte,ite_eq_left ⟨by dsimp [Tma.Descriptor2D.bytes]; omega,hb⟩]
  simp only [Tma.xAt,Tma.yAt,Int.zero_add,← Nat.cast_add,Int.toNat_natCast]
  congr 2
  omega

def dataRepresentedInitial (a : TileA) (b : TileB) (tiles : Nat)
    (frame : Location → Symbolic.Byte) (loc : Location) : Symbolic.Byte :=
  if loc.space = .global then
    if 4096 ≤ loc.address ∧ loc.address < 4224 then .tensorMapPart (aView 65536 tiles) (loc.address-4096)
    else if 4224 ≤ loc.address ∧ loc.address < 4352 then .tensorMapPart (bView (dataBBase tiles) tiles) (loc.address-4224)
    else if 65536 ≤ loc.address ∧ loc.address < 65536+2048*tiles then
      let tile := (loc.address-65536)/2048
      Wgmma.tileByte (a tile) (b tile) ((loc.address-65536)%2048)
    else if dataBBase tiles ≤ loc.address ∧ loc.address < dataBBase tiles+256*tiles then
      let tile := (loc.address-dataBBase tiles)/256
      Wgmma.tileByte (a tile) (b tile) (2048+(loc.address-dataBBase tiles)%256)
    else frame loc
  else frame loc

def dataMaps (tiles address : Nat) : Option Tma.Descriptor2D :=
  if address = 4096 then some (aView 65536 tiles) else if address = 4224 then some (bView (dataBBase tiles) tiles) else none

theorem data_initial_descriptor_a (a b tiles frame) :
    TensorMap.Stored (dataRepresentedInitial a b tiles frame) ⟨.global,4096⟩ (aView 65536 tiles) := by
  intro offset ho
  have h : 4096 ≤ 4096+offset ∧ 4096+offset < 4224 := by omega
  simp only [dataRepresentedInitial,Location.add,ite_true,ite_eq_left h,Nat.add_sub_cancel_left]

theorem data_initial_descriptor_b (a b tiles frame) :
    TensorMap.Stored (dataRepresentedInitial a b tiles frame) ⟨.global,4224⟩ (bView (dataBBase tiles) tiles) := by
  intro offset ho
  have ha : ¬(4096 ≤ 4224+offset ∧ 4224+offset < 4224) := by omega
  have hb : 4224 ≤ 4224+offset ∧ 4224+offset < 4352 := by omega
  simp only [dataRepresentedInitial,Location.add,ite_true,ite_eq_right ha,ite_eq_left hb,Nat.add_sub_cancel_left]

theorem data_initial_a_byte (a b tiles tile frame) (ht : tile < tiles) (offset : Fin 2048) :
    dataRepresentedInitial a b tiles frame ⟨.global,65536+2048*tile+offset.val⟩ =
      Wgmma.tileByte (a tile) (b tile) offset.val := by
  have ho := offset.isLt
  have hd : ¬(4096 ≤ 65536+2048*tile+offset.val ∧ 65536+2048*tile+offset.val < 4224) := by omega
  have he : ¬(4224 ≤ 65536+2048*tile+offset.val ∧ 65536+2048*tile+offset.val < 4352) := by omega
  have ha : 65536 ≤ 65536+2048*tile+offset.val ∧ 65536+2048*tile+offset.val < 65536+2048*tiles := by omega
  have hdiv : (65536+2048*tile+offset.val-65536)/2048 = tile := by omega
  have hmod : (65536+2048*tile+offset.val-65536)%2048 = offset.val := by omega
  simp only [dataRepresentedInitial,ite_true,ite_eq_right hd,ite_eq_right he,ite_eq_left ha,hdiv,hmod]

theorem data_initial_b_byte (a b tiles tile frame) (ht : tile < tiles) (offset : Fin 256) :
    dataRepresentedInitial a b tiles frame ⟨.global,dataBBase tiles+256*tile+offset.val⟩ =
      Wgmma.tileByte (a tile) (b tile) (2048+offset.val) := by
  have ho := offset.isLt
  have hbase : 65536 ≤ dataBBase tiles := by dsimp [dataBBase]; omega
  have hd : ¬(4096 ≤ dataBBase tiles+256*tile+offset.val ∧ dataBBase tiles+256*tile+offset.val < 4224) := by omega
  have he : ¬(4224 ≤ dataBBase tiles+256*tile+offset.val ∧ dataBBase tiles+256*tile+offset.val < 4352) := by omega
  have ha : ¬(65536 ≤ dataBBase tiles+256*tile+offset.val ∧ dataBBase tiles+256*tile+offset.val < 65536+2048*tiles) := by dsimp [dataBBase]; omega
  have hb : dataBBase tiles ≤ dataBBase tiles+256*tile+offset.val ∧ dataBBase tiles+256*tile+offset.val < dataBBase tiles+256*tiles := by omega
  have hdiv : (dataBBase tiles+256*tile+offset.val-dataBBase tiles)/256 = tile := by omega
  have hmod : (dataBBase tiles+256*tile+offset.val-dataBBase tiles)%256 = offset.val := by omega
  simp only [dataRepresentedInitial,ite_true,ite_eq_right hd,ite_eq_right he,ite_eq_right ha,ite_eq_left hb,hdiv,hmod]

theorem data_copy_a_source_byte (a tiles tile) (ht : tile < tiles) (offset : Fin 2048) :
    Tma.sourceByte (dataCopyA a tiles tile).descriptor (dataCopyA a tiles tile).coordinates offset.val =
      some ⟨.global,65536+2048*tile+offset.val⟩ := by
  have hp := packed_slice_source_byte 65536 (8*tiles) 8 (8*tile) offset.val offset.isLt (by omega)
  convert hp using 1 <;> simp [dataCopyA,aView,← Nat.mul_assoc]

theorem data_copy_b_source_byte (b tiles tile) (ht : tile < tiles) (offset : Fin 256) :
    Tma.sourceByte (dataCopyB b tiles tile).descriptor (dataCopyB b tiles tile).coordinates offset.val =
      some ⟨.global,dataBBase tiles+256*tile+offset.val⟩ :=
  packed_slice_source_byte (dataBBase tiles) tiles 1 tile offset.val offset.isLt (by omega)

theorem data_copy_a_payload (a b tiles tile frame) (ht : tile < tiles) (offset : Fin 2048) :
    (dataCopyA a tiles tile).payload[offset.val]? =
      some (Tma.byteValue (dataCopyA a tiles tile).descriptor (dataCopyA a tiles tile).coordinates
        (dataRepresentedInitial a b tiles frame) offset.val) := by
  rw [Tma.copied_byte (data_copy_a_source_byte a tiles tile ht offset),data_initial_a_byte a b tiles tile frame ht offset]
  have hp := HopperStage.transfer_a_payload (a tile) (b tile) offset
  simpa only [dataCopyA,HopperStage.transferView,Wgmma.tileMemory,ite_true,Nat.add_sub_cancel_left] using hp

theorem data_copy_b_payload (a b tiles tile frame) (ht : tile < tiles) (offset : Fin 256) :
    (dataCopyB b tiles tile).payload[offset.val]? =
      some (Tma.byteValue (dataCopyB b tiles tile).descriptor (dataCopyB b tiles tile).coordinates
        (dataRepresentedInitial a b tiles frame) offset.val) := by
  rw [Tma.copied_byte (data_copy_b_source_byte b tiles tile ht offset),data_initial_b_byte a b tiles tile frame ht offset]
  have hp := HopperStage.transfer_b_payload (a tile) (b tile) offset
  have hs : 2064+offset.val-16 = 2048+offset.val := by omega
  simpa only [dataCopyB,HopperStage.transferView,Wgmma.tileMemory,ite_true,hs] using hp

theorem data_transfer_a_read_location (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) (offset : Fin 2048) :
    Tma.readLocation (dataCompleteCandidate a b tiles).view (dataCopyAId a b tiles tile) offset.val =
      some ⟨.global,65536+2048*tile+offset.val⟩ := by
  rw [Tma.readLocation,data_source_copy_a a b tiles tile ht hb]
  exact data_copy_a_source_byte a tiles tile ht offset

theorem data_transfer_b_read_location (a b tiles tile) (ht : tile < tiles) (hb : tiles ≤ 2^28) (offset : Fin 256) :
    Tma.readLocation (dataCompleteCandidate a b tiles).view (dataCopyBId a b tiles tile) offset.val =
      some ⟨.global,dataBBase tiles+256*tile+offset.val⟩ := by
  rw [Tma.readLocation,data_source_copy_b a b tiles tile ht hb]
  exact data_copy_b_source_byte b tiles tile ht offset

end
end Ptx.Kernels.HopperDoubleBuffer
