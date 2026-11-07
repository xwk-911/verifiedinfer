import Ptx.Kernels.AmpereTiledWitnessOracle

/-! Actual byte-access inversions and truthful constructed payloads, without
assuming memory consistency or invoking the universal correctness theorem. -/
namespace Ptx.AmpereTiledWitnessAccesses
open Ptx.ISA Ptx.Ampere Ptx.AmpereTiledSpec Ptx.AmpereTiledTrace Ptx.AmpereTiledEvents Ptx.AmpereTiledGraph
open Ptx.AmpereTiledWitnessOracle Ptx.AmpereTiledProducer
noncomputable section

theorem copy_actual {cfg launch a b} (hp : Pre cfg a b launch) (ha : Active cfg) {id : ThreadId}
    (hv : id.Valid launch.geometry) {phase : Nat} (hphase : phase < cfg.k/16) (part : Fin 3) :
    (execution cfg launch a b).copyAt ⟨id,3*phase+part.val⟩ =
      some (operationAt cfg (context launch id) (oracle cfg launch a b id) (replies cfg launch a b id) phase part) := by
  have he := AmpereTiledWitnessOracle.phase_event hp ha hv hphase (by have hi := part.isLt; omega : part.val < 17)
  rw [AmpereTiledInventory.phase_issue] at he
  exact event_issue_has_copy (source hp ha).formed he

theorem copy_shape {cfg launch a b operation op} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hc : (execution cfg launch a b).copyAt operation = some op) :
    ∃ id, id.Valid launch.geometry ∧ ∃ phase, phase < cfg.k/16 ∧ ∃ part : Fin 3,
      operation = ⟨id,3*phase+part.val⟩ ∧
      op = operationAt cfg (context launch id) (oracle cfg launch a b id) (replies cfg launch a b id) phase part := by
  obtain ⟨t,ht,_,phase,hphase,part,hoperation,_⟩ := copy_cases (source hp ha) hc
  have hv := ((source hp ha).formed.2.2.1 t ht).1
  have hc' := copy_actual hp ha hv hphase part
  rw [hoperation] at hc
  exact ⟨t.id,hv,phase,hphase,part,hoperation,Option.some.inj (hc.symm.trans hc')⟩

theorem read_cases {cfg launch a b node loc value} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hr : (execution cfg launch a b).readByte node loc = some value) :
    (∃ id, id.Valid launch.geometry ∧ ∃ phase, phase < cfg.k/16 ∧ ∃ reg : Fin 6,
      node = .thread ⟨id,17*phase+7+reg.val⟩ ∧
      Ptx.Event.payloadByte (AmpereTiledInventory.readBase (context launch id) reg)
        (AmpereTiledInventory.readPair (replies cfg launch a b id) phase reg).encode loc = some value) ∨
    (∃ operation op, node = .copyRead operation ∧ (execution cfg launch a b).copyAt operation = some op ∧
      Ptx.Event.payloadByte op.src op.bytes loc = some value) := by
  cases node with
  | copyWrite operation =>
    cases hc : (execution cfg launch a b).copyAt operation <;>
      simp [Candidate.readByte,Candidate.memoryKind,hc,Ptx.Event.Kind.readByte] at hr
  | copyRead operation =>
    cases hc : (execution cfg launch a b).copyAt operation with
    | none => simp [Candidate.readByte,Candidate.memoryKind,hc] at hr
    | some op => exact .inr ⟨operation,op,rfl,hc,by simpa [Candidate.readByte,Candidate.memoryKind,hc,Ptx.Event.Kind.readByte] using hr⟩
  | thread event =>
    cases hk : (execution cfg launch a b).memoryKind (.thread event) with
    | none => simp [Candidate.readByte,hk] at hr
    | some kind =>
      cases kind with
      | read base bytes =>
        have hpayload : Ptx.Event.payloadByte base bytes loc = some value := by simpa [Candidate.readByte,hk,Ptx.Event.Kind.readByte] using hr
        obtain ⟨t,ht,hid,hget⟩ := eventAt_trace (event_of_thread_kind hk)
        obtain ⟨id,hmem,rfl⟩ := List.mem_map.mp ht
        obtain ⟨phase,hphase,reg,hserial,rfl,rfl⟩ := AmpereTiledInventory.read_cases hget
        refine .inl ⟨id,Geometry.mem_threads.mp hmem,phase,hphase,reg,?_,hpayload⟩
        cases event
        simp_all [AmpereTiledSourceCandidate.trace,Nat.add_assoc]
      | rmw scope base bytes =>
        exact (AmpereTiledGraph.no_rmw (source hp ha) (.thread event) ⟨scope,base,bytes,hk⟩).elim
      | _ => simp [Candidate.readByte,hk,Ptx.Event.Kind.readByte] at hr

theorem pair_half {cfg launch a b id} (hp : Pre cfg a b launch) (hv : id.Valid launch.geometry)
    (phase : Nat) (reg : Fin 6) (half : Fin 2) :
    (AmpereTiledInventory.readPair (replies cfg launch a b id) phase reg).half half =
      AmpereTiledInputRead.expected a b id phase reg half := by
  have hv' : id.Valid (geometry cfg) := by simpa only [hp.2.2.1] using hv
  fin_cases reg
  · simpa [AmpereTiledInventory.readPair,replies,aPair,lane_eq hv'] using
      (AmpereTiledFragmentInputs.expected_a a b id hv' phase 0 half).symm
  · simpa [AmpereTiledInventory.readPair,replies,aPair,lane_eq hv'] using
      (AmpereTiledFragmentInputs.expected_a a b id hv' phase 1 half).symm
  · simpa [AmpereTiledInventory.readPair,replies,aPair,lane_eq hv'] using
      (AmpereTiledFragmentInputs.expected_a a b id hv' phase 2 half).symm
  · simpa [AmpereTiledInventory.readPair,replies,aPair,lane_eq hv'] using
      (AmpereTiledFragmentInputs.expected_a a b id hv' phase 3 half).symm
  · simpa [AmpereTiledInventory.readPair,replies,bPair,lane_eq hv'] using
      (AmpereTiledFragmentInputs.expected_b a b id hv' phase 0 half).symm
  · simpa [AmpereTiledInventory.readPair,replies,bPair,lane_eq hv'] using
      (AmpereTiledFragmentInputs.expected_b a b id hv' phase 1 half).symm

theorem shared_payload_initial {cfg launch a b id loc value} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hv : id.Valid launch.geometry) {phase : Nat} (hphase : phase < cfg.k/16) (reg : Fin 6)
    (hr : Ptx.Event.payloadByte (AmpereTiledInventory.readBase (context launch id) reg)
      (AmpereTiledInventory.readPair (replies cfg launch a b id) phase reg).encode loc = some value) :
    ∃ offset : Fin 4, loc = (AmpereTiledInventory.readBase (context launch id) reg).add offset.val ∧
      value = launch.initial ((inputBase cfg id phase reg).add offset.val) := by
  obtain ⟨offset,ho,rfl⟩ := Ptx.Event.payload_location hr
  have hoff : offset < 4 := by simpa only [PackedF16.encode_size] using ho
  let half : Fin 2 := ⟨offset/2,by omega⟩
  let byteOffset : Fin 2 := ⟨offset%2,by omega⟩
  have he : 2*half.val+byteOffset.val = offset := by dsimp [half,byteOffset]; omega
  have hb := PackedF16.half_byte (AmpereTiledInventory.readPair (replies cfg launch a b id) phase reg)
    (AmpereTiledInventory.readBase (context launch id) reg) half byteOffset
  rw [he,hr] at hb
  have hi := AmpereTiledInputRead.initial_half_byte (source hp ha) hp.2.1 hv hphase reg half byteOffset
  rw [he] at hi
  rw [pair_half hp hv] at hb
  exact ⟨⟨offset,hoff⟩,rfl,(Option.some.inj hb).trans hi.symm⟩

theorem copy_read_initial {cfg launch a b operation op loc value} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hc : (execution cfg launch a b).copyAt operation = some op)
    (hr : Ptx.Event.payloadByte op.src op.bytes loc = some value) : value = launch.initial loc := by
  obtain ⟨id,hv,phase,hphase,part,_,rfl⟩ := copy_shape hp ha hc
  have hv' : (context launch id).id.Valid (geometry cfg) := by simpa only [context,hp.2.2.1] using hv
  rw [operation_source hp.1 _ _ _ hv' ha phase hphase part] at hr
  change Ptx.Event.payloadByte ⟨.global,AmpereTiledBounds.copyStart cfg (context launch id) phase part⟩
    (payload cfg launch id phase part) loc = some value at hr
  obtain ⟨offset,ho,rfl⟩ := Ptx.Event.payload_location hr
  have hoff : offset < 8 := by simpa only [payload,List.length_ofFn] using ho
  rw [Ptx.Event.payloadByte_offset,payload_byte cfg launch id phase part ⟨offset,hoff⟩] at hr
  exact (Option.some.inj hr).symm

theorem copy_write_byte {cfg launch a b id} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hv : id.Valid launch.geometry) {phase : Nat} (hphase : phase < cfg.k/16) (part : Fin 3) (offset : Fin 8) :
    (execution cfg launch a b).writeByte (.copyWrite ⟨id,3*phase+part.val⟩)
      ⟨.shared id.cta,AmpereTiledSharedWriters.copyBase id part+offset.val⟩ =
      some (launch.initial ⟨.global,AmpereTiledBounds.copyStart cfg (context launch id) phase part+offset.val⟩) := by
  have hv' : (context launch id).id.Valid (geometry cfg) := by simpa only [context,hp.2.2.1] using hv
  have hcopy := copy_actual hp ha hv hphase part
  simp only [Candidate.writeByte,Candidate.memoryKind,hcopy,Option.map_some,Option.bind_some,Ptx.Event.Kind.writeByte]
  rw [operation_destination (cfg := cfg) _ _ _ hv' phase part]
  change Ptx.Event.payloadByte ⟨.shared id.cta,AmpereTiledSharedWriters.copyBase id part⟩
    (payload cfg launch id phase part) _ = _
  change Ptx.Event.payloadByte _ _ ((⟨.shared id.cta,AmpereTiledSharedWriters.copyBase id part⟩ : Location).add offset.val) = _
  rw [Ptx.Event.payloadByte_offset]
  exact payload_byte cfg launch id phase part offset

theorem shared_source_write {cfg launch a b id loc value} (hp : Pre cfg a b launch) (ha : Active cfg)
    (hv : id.Valid launch.geometry) {phase : Nat} (hphase : phase < cfg.k/16) (reg : Fin 6)
    (hr : Ptx.Event.payloadByte (AmpereTiledInventory.readBase (context launch id) reg)
      (AmpereTiledInventory.readPair (replies cfg launch a b id) phase reg).encode loc = some value) :
    (execution cfg launch a b).writeByte (.copyWrite ⟨producer id reg,3*phase+(part reg).val⟩) loc = some value := by
  obtain ⟨offset,hl,hvalue⟩ := shared_payload_initial hp ha hv hphase reg hr
  have hv' : (context launch id).id.Valid (geometry cfg) := by simpa only [context,hp.2.2.1] using hv
  have hproducer : (producer id reg).Valid launch.geometry := by simpa only [hp.2.2.1,context] using producer_valid hv' reg
  let copiedOffset : Fin 8 := ⟨wordOffset id+offset.val,by have hi := offset.isLt; dsimp [wordOffset]; omega⟩
  have hw := copy_write_byte hp ha hproducer hphase (part reg) copiedOffset
  have hloc : loc = ⟨.shared (producer id reg).cta,AmpereTiledSharedWriters.copyBase (producer id reg) (part reg)+copiedOffset.val⟩ := by
    rw [hl,read_destination hv' reg]
    simp [Location.add,copiedOffset,context,producer,Nat.add_assoc]
  have hinput : (⟨.global,AmpereTiledBounds.copyStart cfg (context launch (producer id reg)) phase (part reg)+copiedOffset.val⟩ : Location) =
      (inputBase cfg id phase reg).add offset.val := by
    have hh := input_address cfg (context launch id) phase reg
    change (⟨.global,AmpereTiledBounds.copyStart cfg (context launch (producer id reg)) phase (part reg)⟩ : Location).add
      (wordOffset id) = inputBase cfg id phase reg at hh
    rw [← hh]
    simp [Location.add,copiedOffset,Nat.add_assoc]
  rw [hinput,← hvalue,← hloc] at hw
  exact hw

end
end Ptx.AmpereTiledWitnessAccesses
