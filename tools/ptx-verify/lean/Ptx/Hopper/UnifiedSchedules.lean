import Ptx.Hopper.UnifiedCollective
import Ptx.Hopper.WgmmaSignatureRules

/-! A finite metadata checker for aligned collective schedules. Every lane of
each participating physical warpgroup must have the same full fence/MMA/
commit/wait sequence, retaining actual PC and dynamic operation metadata.
Ordinary-only threads need not form a warpgroup. This is a collective
participation component, not memory publication or full SIMT/control admission.
-/
namespace Ptx.Hopper.Unified
open Ptx.ISA
noncomputable section

def ThreadTrace.nativeSchedule (trace : ThreadTrace) : List Wgmma.SourceSignature := Wgmma.eventSchedule trace.events
def ThreadTrace.alignedSchedule (trace : ThreadTrace) : List Wgmma.SourceSignature := trace.nativeSchedule.map Wgmma.alignedSignature
def ThreadTrace.linear (trace : ThreadTrace) (block : Dim3) : Nat := trace.id.tid.linear block
def participantMatches (block : Dim3) (trace peer : ThreadTrace) (lane : Wgmma.Lane) : Bool :=
  peer.id.cta == trace.id.cta && peer.linear block == 128*(trace.linear block/128)+lane.val &&
    peer.alignedSchedule == trace.alignedSchedule
def checkSchedules (block : Dim3) (candidate : Candidate) : Bool :=
  candidate.traces.all (fun trace => trace.nativeSchedule.isEmpty ||
    (List.ofFn (fun lane : Wgmma.Lane => lane)).all (fun lane => candidate.traces.any (fun peer => participantMatches block trace peer lane)))
def SchedulesAdmitted (block : Dim3) (candidate : Candidate) : Prop := checkSchedules block candidate = true
instance (block candidate) : Decidable (SchedulesAdmitted block candidate) := by unfold SchedulesAdmitted; infer_instance

theorem participant_matches_iff (block trace peer lane) : participantMatches block trace peer lane = true ↔
    peer.id.cta = trace.id.cta ∧ peer.linear block = 128*(trace.linear block/128)+lane.val ∧ peer.alignedSchedule = trace.alignedSchedule := by
  simp only [participantMatches,Bool.and_eq_true,beq_iff_eq,and_assoc]
theorem schedules_admitted_of_participants {block candidate}
    (h : ∀ trace ∈ candidate.traces, trace.nativeSchedule ≠ [] → ∀ lane : Wgmma.Lane,
      ∃ peer ∈ candidate.traces, peer.id.cta = trace.id.cta ∧
        peer.linear block = 128*(trace.linear block/128)+lane.val ∧ peer.alignedSchedule = trace.alignedSchedule) :
    SchedulesAdmitted block candidate := by
  apply List.all_eq_true.mpr
  intro trace ht
  by_cases hn : trace.nativeSchedule = []
  · simp only [hn,List.isEmpty_nil,Bool.true_or]
  · apply Bool.or_eq_true_iff.mpr
    right
    apply List.all_eq_true.mpr
    intro lane _
    obtain ⟨peer,hp,hc,hl,hs⟩ := h trace ht hn lane
    exact List.any_eq_true.mpr ⟨peer,hp,(participant_matches_iff block trace peer lane).mpr ⟨hc,hl,hs⟩⟩
theorem schedules_have_all_participants {block candidate} (h : SchedulesAdmitted block candidate)
    {trace} (ht : trace ∈ candidate.traces) (hn : trace.nativeSchedule ≠ []) (lane : Wgmma.Lane) :
    ∃ peer ∈ candidate.traces, peer.id.cta = trace.id.cta ∧
      peer.linear block = 128*(trace.linear block/128)+lane.val ∧ peer.alignedSchedule = trace.alignedSchedule := by
  have hc := List.all_eq_true.mp h trace ht
  have he : trace.nativeSchedule.isEmpty ≠ true := fun he => hn (List.nil_of_isEmpty he)
  have ha := (Bool.or_eq_true_iff.mp hc).resolve_left he
  have hp := List.all_eq_true.mp ha lane (List.mem_ofFn.mpr ⟨lane,rfl⟩)
  obtain ⟨peer,hm,hs⟩ := List.any_eq_true.mp hp
  exact ⟨peer,hm,(participant_matches_iff block trace peer lane).mp hs⟩
theorem trace_schedule_has_checked_replay {code params block trace}
    (hp : Produced code params block trace) :
    ∃ located, Wgmma.runLocated {id := trace.id,params := params,block := block} trace.oracle code trace.count {} =
      .ok (trace.final,located) ∧ Wgmma.schedule located = trace.nativeSchedule := by
  obtain ⟨located,hr,he⟩ := Wgmma.run_located_exists hp
  exact ⟨located,hr,by rw [Wgmma.located_schedule_sound hr,he]; rfl⟩
theorem source_signature_actual_pc {candidate code launch id event signature}
    (hw : WellFormed code launch candidate) (he : candidate.eventAt id = some event)
    (hs : Wgmma.eventSignature event = some signature) :
    candidate.sourcePC code launch.params launch.geometry.block id = some signature.pc := by
  obtain ⟨located,hl,hk,oracle,before,after,emitted,hstep,hm,hpc⟩ := source_event hw he
  cases hc : Wgmma.collective event with
  | none => simp [Wgmma.eventSignature,hc] at hs
  | some pair =>
    rcases pair with ⟨mark,kind⟩
    have hm := Wgmma.step_collective_mark hstep hm (by simpa only [hk] using hc)
    simp only [Wgmma.eventSignature,hc,Option.map_some,Option.some.injEq] at hs
    subst signature
    simp only [Candidate.sourcePC,hl,Option.map_some]
    exact congrArg some (hpc.trans hm.1.symm)

end
end Ptx.Hopper.Unified
