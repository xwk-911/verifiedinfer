import Ptx.Kernels.AmpereTiledMemory
import Ptx.Kernels.AmpereTiledAccesses

/-! Derive the live copy owner and global source address for each packed
shared read. These facts apply to arbitrary completed actual source candidates;
no read answer, source choice or extra synchronization is assumed. -/
namespace Ptx.AmpereTiledProducer
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledEvents Ptx.AmpereTiledGraph
noncomputable section

def producer (id : ThreadId) (reg : Fin 6) : ThreadId :=
  {id with tid := {id.tid with x := id.tid.x/2+2*(if reg.val < 4 then reg.val/2 else reg.val-4)}}
def part (reg : Fin 6) : Fin 3 := ⟨if reg.val < 4 then reg.val%2 else 2,by split <;> omega⟩
def wordOffset (id : ThreadId) : Nat := 4*(id.tid.x%2)
def inputBase (cfg : Config) (id : ThreadId) (phase : Nat) (reg : Fin 6) : Location :=
  if reg.val < 4 then aLocation cfg (16*id.cta.y+id.tid.y+8*(reg.val%2)) (16*phase+2*id.tid.x+8*(reg.val/2))
  else bLocation cfg (16*phase+2*id.tid.x+8*(reg.val-4)) (8*id.cta.x+id.tid.y)

theorem producer_valid {cfg : Config} {id : ThreadId} (hv : id.Valid (geometry cfg)) (reg : Fin 6) :
    (producer id reg).Valid (geometry cfg) := by
  have hx : id.tid.x < 4 := hv.2.1
  have hi := reg.isLt
  refine ⟨hv.1,?_,hv.2.2⟩
  change id.tid.x/2+2*(if reg.val < 4 then reg.val/2 else reg.val-4) < 4
  split <;> omega

theorem read_destination {cfg : Config} {ctx : Scalar.Context} (hv : ctx.id.Valid (geometry cfg)) (reg : Fin 6) :
    AmpereTiledInventory.readBase ctx reg =
      ⟨.shared ctx.id.cta,AmpereTiledSharedWriters.copyBase (producer ctx.id reg) (part reg)+wordOffset ctx.id⟩ := by
  have hx : ctx.id.tid.x < 4 := hv.2.1
  have hy : ctx.id.tid.y < 8 := hv.2.2.1
  have hs := AmpereTiledAddressRules.shared_formulas ctx hx hy
  fin_cases reg <;>
    simp [AmpereTiledInventory.readBase,hs.2.2.2.1,hs.2.2.2.2,AmpereTiledSharedWriters.copyBase,
      producer,part,wordOffset,wrap] <;> omega

theorem input_address (cfg : Config) (ctx : Scalar.Context) (phase : Nat) (reg : Fin 6) :
    (⟨.global,AmpereTiledBounds.copyStart cfg {ctx with id := producer ctx.id reg} phase (part reg)⟩ : Location).add
      (wordOffset ctx.id) = inputBase cfg ctx.id phase reg := by
  have hquot : 4*(ctx.id.tid.x/2)+2*(ctx.id.tid.x%2) = 2*ctx.id.tid.x := by omega
  fin_cases reg <;>
    simp [inputBase,AmpereTiledBounds.copyStart,producer,part,wordOffset,aLocation,bLocation,Location.add] <;>
    nlinarith

theorem copy_metadata {cfg launch candidate} (h : SourceInfo cfg launch candidate) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase : Nat} (hp : phase < cfg.k/16) (i : Fin 3) :
    ∃ op, candidate.copyAt ⟨id,3*phase+i.val⟩ = some op ∧
      op.src = ⟨.global,AmpereTiledBounds.copyStart cfg (context launch id) phase i⟩ ∧
      op.dst = ⟨.shared id.cta,AmpereTiledSharedWriters.copyBase id i⟩ ∧ op.bytes.length = 8 := by
  obtain ⟨t,ht,hid,r,he⟩ := phase_view h hv hp (by have hh := i.isLt; omega : i.val < 17)
  subst id
  have hv' : (context launch t.id).id.Valid (geometry cfg) := by simpa only [h.geometry,context] using hv
  rw [AmpereTiledInventory.phase_issue] at he
  exact ⟨_,event_issue_has_copy h.formed he,operation_source h.layout _ _ r hv' h.active phase hp i,
    operation_destination _ _ r hv' phase i,operation_size _ _ _ r phase hp i⟩

theorem read_input_byte {cfg launch candidate rf co} (h : SourceInfo cfg launch candidate)
    (hm : MemoryConstraints candidate launch.initial rf co) {id : ThreadId} (hv : id.Valid launch.geometry)
    {phase : Nat} (hp : phase < cfg.k/16) (reg : Fin 6) (offset : Fin 4) {observed}
    (hr : candidate.readByte (.thread ⟨id,17*phase+7+reg.val⟩)
      ((AmpereTiledInventory.readBase (context launch id) reg).add offset.val) = some observed) :
    observed = launch.initial ((inputBase cfg id phase reg).add offset.val) := by
  have hvr : (context launch id).id.Valid (geometry cfg) := by simpa only [h.geometry,context] using hv
  have hvp : (producer id reg).Valid launch.geometry := by simpa only [h.geometry,context] using producer_valid hvr reg
  obtain ⟨op,hcopy,hsrc,hdst,hlen⟩ := copy_metadata h hvp hp (part reg)
  have hoff : wordOffset id+offset.val < op.bytes.length := by rw [hlen]; have hh := offset.isLt; dsimp [wordOffset]; omega
  let loc := (AmpereTiledInventory.readBase (context launch id) reg).add offset.val
  have hloc : loc = op.dst.add (wordOffset id+offset.val) := by
    rw [hdst]
    dsimp only [loc]
    rw [read_destination hvr reg]
    simp [Location.add,Nat.add_assoc,context,producer]
  have hw : candidate.writeByte (.copyWrite ⟨producer id reg,3*phase+(part reg).val⟩) loc =
      some op.bytes[wordOffset id+offset.val] := by
    simp only [Candidate.writeByte,Candidate.memoryKind,hcopy,Option.map_some,Option.bind_some,
      Ptx.Event.Kind.writeByte,hloc,Ptx.Event.payloadByte_offset,List.getElem?_eq_getElem hoff]
  have hvalue := AmpereTiledMemory.current_copy_value h hm hvp hv rfl hp (part reg) reg rfl hw hr
  have hinit := AmpereTiledMemory.copy_payload_initial h hm hcopy hoff
  have hadd : op.src.add (wordOffset id+offset.val) = (inputBase cfg id phase reg).add offset.val := by
    rw [hsrc]
    have he := input_address cfg (context launch id) phase reg
    change (⟨.global,AmpereTiledBounds.copyStart cfg (context launch (producer id reg)) phase (part reg)⟩ : Location).add
      (wordOffset id) = inputBase cfg id phase reg at he
    rw [← he]
    simp [Location.add,Nat.add_assoc]
  exact hvalue.trans (hinit.trans (congrArg launch.initial hadd))

end
end Ptx.AmpereTiledProducer
