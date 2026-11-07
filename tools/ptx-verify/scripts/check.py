"""Run frontend, Lean, and rejection checks for the verifier examples."""

import os
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from check_coverage import main as check_coverage

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
CASES = {
    "release_acquire_message": "ReleaseAcquireMessage",
    "copy": "Copy",
    "byte_value_pipeline": "ByteValuePipeline",
    "shuffle_up": "ShuffleUp",
    "shuffle_down": "ShuffleDown",
    "shuffle_bfly": "ShuffleBfly",
    "shuffle_idx": "ShuffleIdx",
    "shuffle_pair": "ShufflePair",
    "shared_swap": "SharedSwap",
    "loop": "Loop",
    "missing_sync": "MissingSync",
    "out_of_bounds": "OutOfBounds",
    "barrier_publish": "BarrierPublish",
    "divergent_barrier": "DivergentBarrier",
    "float_fma": "FloatFma",
    "float_literals": "FloatLiterals",
    "scalar_matmul": "ScalarMatmul",
    "atomic_dispatch": "AtomicDispatch",
    "scalar_flash_attention": "ScalarFlashAttention",
    "moe_route": "MoeRoute",
    "moe_experts": "MoeExperts",
    "moe_combine": "MoeCombine",
    "cp_async_copy": "CpAsyncCopy",
    "cp_async_groups": "CpAsyncGroups",
    "cp_async_no_wait": "CpAsyncNoWait",
    "mma_probe": "MmaProbe",
    "ampere_tiled_matmul": "AmpereTiledMatmul",
    "hopper_mbarrier": "HopperMbarrier",
    "hopper_mbarrier_no_complete": "HopperMbarrierNoComplete",
    "hopper_mbarrier_peers": "HopperMbarrierPeers",
    "hopper_mbarrier_cycle": "HopperMbarrierCycle",
    "hopper_tma_copy": "HopperTmaCopy",
    "hopper_tma_publish": "HopperTmaPublish",
    "wgmma_probe": "WgmmaProbe",
    "hopper_gemm_stage": "HopperGemmStage",
    "hopper_collective_cycle": "HopperCollectiveCycle",
    "hopper_double_buffer_gemm": "HopperDoubleBufferGemm",
}
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
NEGATIVE_CASES = {
    "out_of_bounds": (
        "run Generated.out_of_bounds.program (List.replicate 11 (.thread 0)) copyInitial"
    ),
    "missing_barrier": (
        "run Generated.missing_sync.program missingSyncSchedule sharedInitial"
    ),
    "early_reclaim": "earlyReclaim",
    "partial_barrier": "SharedInstances.partialArrival.bind release",
    "stale_event_reclaim": (
        "Async.run (Async.initial 1 [42]) "
        "[.use 0 0,.record 0 9,.device 0,.acquire 9,.use 0 0,.acquire 9,.reclaim 0]"
    ),
    "remaining_reader_reclaim": (
        "Async.run (Async.initial 2 [42]) "
        "[.use 0 0,.use 1 0,.record 0 7,.device 0,.acquire 7,.reclaim 0]"
    ),
    "host_write_inflight": "Async.run (Async.initial 1 [42]) [.use 0 0,.write 0 99]",
    'byte_protocol_early_acquire_accepted': 'IrisExecution.run (ByteAuthorityHeap.transition ByteProtocolTests.ctx) (ByteAuthorityHeap.protocolActions [.host (.acquire 0)]) (ByteProtocolTests.state (Hopper.Progress.Present ByteRetirementTests.rmwCandidate))',
    'byte_protocol_device_completion_returns_loan': 'IrisExecution.run (ByteAuthorityHeap.transition ByteProtocolTests.ctx) (ByteAuthorityHeap.protocolActions [.host (.reclaim 0)]) ByteProtocolTests.afterDeviceState',
    'byte_protocol_device_completion_allows_write': 'IrisExecution.run (ByteAuthorityHeap.transition ByteProtocolTests.ctx) (ByteAuthorityHeap.protocolActions [.host (.write 0 99)]) ByteProtocolTests.afterDeviceState',
    'byte_protocol_duplicate_record_accepted': 'IrisExecution.run (ByteAuthorityHeap.transition ByteProtocolTests.ctx) (ByteAuthorityHeap.protocolActions [.host (.record 0 0)]) (ByteProtocolTests.state (Hopper.Progress.Present ByteRetirementTests.rmwCandidate))',
    'byte_protocol_stream_wait_bypassed': 'IrisExecution.run (ByteAuthorityHeap.transition ByteProtocolTests.ctx) (ByteAuthorityHeap.protocolActions [.device 1]) ByteProtocolTests.waitingState',
    'byte_protocol_invalid_stream_accepted': 'IrisExecution.run (ByteAuthorityHeap.transition ByteProtocolTests.ctx) (ByteAuthorityHeap.protocolActions [.device 99]) (ByteProtocolTests.state (Hopper.Progress.Present ByteRetirementTests.rmwCandidate))',
}
NEGATIVE_PROPOSITIONS = {
    'ordered_release_scope_is_erased': '((OrderedTests.candidate.kindAt OrderedTests.flagWrite).map Ordered.Kind.scope) = some none',
    'ordered_acquire_is_silently_relaxed': '((OrderedTests.candidate.kindAt OrderedTests.flagRead).map Ordered.Kind.order) = some Ordered.Order.relaxed',
    'ordered_polling_retry_loses_a_load': 'OrderedTests.retryTrace.final.core.queries = 2',
    'ordered_consumer_payload_has_no_oracle_query': '(OrderedTests.trace 1 12).final.core.queries = 1',
    'shuffle_array_domain_silently_drops_a_word': '(Kernels.ShuffleProbe.arrayDomain ShuffleProbeTests.input ShuffleLaunchTests.launch).length = 508',
    'shuffle_array_domain_flag_byte_has_wrong_address': '((Kernels.ShuffleProbe.arrayDomain ShuffleProbeTests.input ShuffleLaunchTests.launch)[4]?.map ISA.Location.address) = some 4099',
    'shuffle_array_domain_includes_right_guard': '((Kernels.ShuffleProbe.arrayDomain ShuffleProbeTests.input ShuffleLaunchTests.launch)[512]?).isSome = true',
    'shuffle_array_domain_includes_left_guard': '((Kernels.ShuffleProbe.arrayDomain ShuffleProbeTests.input ShuffleLaunchTests.launch)[0]?.map ISA.Location.address) = some 4095',
    'shuffle_probe_3d_index_collapses_to_x': 'Kernels.ShuffleProbe.rawIndex ShuffleProbeTests.ctx = 3',
    'shuffle_probe_input_wrap_erased': 'Kernels.ShuffleProbe.inputWord ShuffleProbeTests.input ShuffleProbeTests.ctx = 4294967307',
    'shuffle_probe_false_predicate_exports_one': 'ShuffleProbeTests.flagBytes false = [1,0,0,0]',
    'shuffle_probe_true_predicate_exports_zero': 'ShuffleProbeTests.flagBytes true = [0,0,0,0]',
    'shuffle_probe_ordinary_graph_retains_shuffle': '(Shuffle.ordinaryEvents (Kernels.ShuffleProbe.events .bfly ShuffleProbeTests.input ShuffleProbeTests.ctx 17 true)).length = 3',
    'shuffle_probe_word_stride_is_four': 'Kernels.ShuffleProbe.address ShuffleProbeTests.input ShuffleProbeTests.ctx = 4204',
    'shuffle_probe_flag_overwrites_value_location': '(Kernels.ShuffleProbe.outputLoc ShuffleProbeTests.input ShuffleProbeTests.ctx 4).address = 4312',
    'shuffle_probe_25_steps_succeed': '(Shuffle.run ShuffleProbeTests.ctx (ShuffleProbeTests.answers 17 true) (Kernels.ShuffleProbe.code .bfly) 25 {}).toOption.isSome = true',
    'shuffle_probe_flag_address_ignores_u64_wrap': '(Kernels.ShuffleProbe.outputLoc ShuffleProbeTests.crossingInput ShuffleProbeTests.crossingContext 4).address = 18446744073709551616',
    'shuffle_probe_selected_value_loses_warp_offset': 'Kernels.ShuffleProbe.expectedWord .bfly ShuffleProbeTests.input ShuffleProbeTests.secondWarpContext = 14',
    'shuffle_probe_up_ignores_lower_clamp': 'Kernels.ShuffleProbe.expectedPredicate .up ShuffleProbeTests.input ShuffleProbeTests.ctx = true',
    'shuffle_completed_execution_accepts_padding': '(Shuffle.run {id := Kernels.ShufflePair.id 0,block := Kernels.ShufflePair.block} (ShuffleUniversalTests.changedAnswers 0) Generated.shuffle_pair.program 4 {}).toOption.isSome = true',
    'shuffle_two_steps_are_already_done': '((Shuffle.run {id := Kernels.ShufflePair.id 0,block := Kernels.ShufflePair.block} (ShuffleUniversalTests.changedAnswers 0) Generated.shuffle_pair.program 2 {}).toOption.map (fun result => result.1.base.core.thread.status)) = some .done',
    'shuffle_reordered_witness_silently_reorders_back': '(ShuffleUniversalTests.reordered.traces.map Shuffle.ThreadTrace.id)[0]? = some (Kernels.ShufflePair.id 0)',
    'shuffle_uses_an_unissued_oracle_query': '(ShuffleUniversalTests.changedTrace 0).final.queries = 2',
    'shuffle_up_underflow_is_saturating': '(Shuffle.select .up 0 1 0).predicate = true',
    'shuffle_down_wraps_at_warp_end': '(Shuffle.select .down 31 1 31).source = 0',
    'shuffle_bfly_forbids_lower_segment': '(Shuffle.select .bfly 16 16 0x100f).predicate = false',
    'shuffle_idx_ignores_segment': '(Shuffle.select .idx 17 20 0x100f).source = 4',
    'shuffle_idx_failed_clamp_uses_remote': '(Shuffle.select .idx 17 31 15).source = 31',
    'shuffle_different_mode_shares_counter': 'Shuffle.generation {visits := Shuffle.advanceVisits {} Kernels.ShufflePair.key : Shuffle.State} ⟨.idx,3⟩ = 1',
    'value_pipeline_first_byte_erased': '(match Hopper.ByteContents.valueAt (Kernels.ByteValuePipeline.afterReader 305419896 305419896) Kernels.ByteValuePipeline.base with | some (.bits value) => value.val | _ => 999999) = 0',
    'value_pipeline_last_byte_erased': '(match Hopper.ByteContents.valueAt (Kernels.ByteValuePipeline.afterReader 305419896 305419896) (Kernels.ByteValuePipeline.base.add 3) with | some (.bits value) => value.val | _ => 999999) = 0',
    'value_pipeline_source_ignores_u32_wrap': 'ISA.declarationLookup "%r" (Kernels.ByteValuePipeline.trace 4294967303 4294967303).final.base.scalar.core.thread.regs = some 4294967303',
    'value_pipeline_read_moved_before_store': '(Generated.byte_value_pipeline.program[2]?.map (fun i => match i with | .load .. => true | _ => false)) = some true',
    'local_value_frame_counter_stays_zero': '(match Hopper.ByteContents.valueAt ByteContentsFootprintTests.framedFinal AtomicMemoryTests.base with | some (.bits value) => value.val | _ => 999999) = 0',
    'local_value_frame_spare_is_clobbered': '(match Hopper.ByteContents.valueAt ByteContentsFootprintTests.framedFinal ByteContentsFootprintTests.spare with | some (.bits value) => value.val | _ => 999999) = 0',
    'byte_contents_actual_rmw_leaves_counter_zero': '(match Hopper.ByteContents.valueAt ByteContentsTests.finalState AtomicMemoryTests.base with | some (.bits value) => value.val | _ => 999999) = 0',
    'byte_contents_actual_rmw_leaves_counter_uninitialized': '(Hopper.ByteContents.valueAt ByteContentsTests.finalState AtomicMemoryTests.base).isNone = true',
    'double_output_domain_omits_frame': 'Kernels.HopperDoubleBuffer.dataOutputDomain.length = 2048',
    'double_output_first_missing': '(⟨.global,8192⟩ : ISA.Location) ∉ Kernels.HopperDoubleBuffer.dataOutputDomain',
    'double_output_last_missing': '(⟨.global,10239⟩ : ISA.Location) ∉ Kernels.HopperDoubleBuffer.dataOutputDomain',
    'double_output_left_frame_missing': '(⟨.global,8188⟩ : ISA.Location) ∉ Kernels.HopperDoubleBuffer.dataOutputDomain',
    'double_output_right_frame_missing': '(⟨.global,10243⟩ : ISA.Location) ∉ Kernels.HopperDoubleBuffer.dataOutputDomain',
    'double_output_before_frame_included': '(⟨.global,8187⟩ : ISA.Location) ∈ Kernels.HopperDoubleBuffer.dataOutputDomain',
    'double_output_after_frame_included': '(⟨.global,10244⟩ : ISA.Location) ∈ Kernels.HopperDoubleBuffer.dataOutputDomain',
    'double_output_shared_in_domain': '(⟨.shared .zero,8192⟩ : ISA.Location) ∈ Kernels.HopperDoubleBuffer.dataOutputDomain',
    'double_output_first_wrong_owner': 'Kernels.HopperDoubleBuffer.dataOutputOwner 8192 = (1,0)',
    'double_output_last_wrong_owner': 'Kernels.HopperDoubleBuffer.dataOutputOwner 10239 = (127,2)',
    'double_output_first_unselected': '(HopperDoubleBufferObservedOutputTests.selection ⟨.global,8192⟩).isSome = false',
    'double_output_last_unselected': '(HopperDoubleBufferObservedOutputTests.selection ⟨.global,10239⟩).isSome = false',
    'double_output_left_frame_written': '(HopperDoubleBufferObservedOutputTests.selection ⟨.global,8191⟩).isSome = true',
    'double_output_right_frame_written': '(HopperDoubleBufferObservedOutputTests.selection ⟨.global,10240⟩).isSome = true',
    'double_output_input_written': '(HopperDoubleBufferObservedOutputTests.selection ⟨.global,65536⟩).isSome = true',
    'double_output_descriptor_written': '(HopperDoubleBufferObservedOutputTests.selection ⟨.global,4096⟩).isSome = true',
    'double_output_shared_written': '(HopperDoubleBufferObservedOutputTests.selection ⟨.shared .zero,8192⟩).isSome = true',
    'double_output_store_serials_alias': 'Kernels.HopperDoubleBuffer.dataStoreId HopperDoubleBufferObservedOutputTests.a HopperDoubleBufferObservedOutputTests.b 3 0 0 = Kernels.HopperDoubleBuffer.dataStoreId HopperDoubleBufferObservedOutputTests.a HopperDoubleBufferObservedOutputTests.b 3 0 3',
    'double_output_selected_wrong_lane': 'HopperDoubleBufferObservedOutputTests.selection ⟨.global,8192⟩ = some (.base (.tma (.source (Kernels.HopperDoubleBuffer.dataStoreId HopperDoubleBufferObservedOutputTests.a HopperDoubleBufferObservedOutputTests.b 3 1 0))))',
    'double_output_selected_wrong_slot': 'HopperDoubleBufferObservedOutputTests.selection ⟨.global,8192⟩ = some (.base (.tma (.source (Kernels.HopperDoubleBuffer.dataStoreId HopperDoubleBufferObservedOutputTests.a HopperDoubleBufferObservedOutputTests.b 3 0 1))))',
    'full_memory_init_does_not_precede_writer': 'HopperDoubleBufferMemoryWitnessTests.coCheck HopperDoubleBufferMemoryWitnessTests.sharedA none (some (HopperDoubleBufferMemoryWitnessTests.firstA 0)) = false',
    'full_memory_old_does_not_precede_reuse': 'HopperDoubleBufferMemoryWitnessTests.coCheck HopperDoubleBufferMemoryWitnessTests.sharedA (some (HopperDoubleBufferMemoryWitnessTests.firstA 0)) (some (HopperDoubleBufferMemoryWitnessTests.firstA 2)) = false',
    'full_memory_reverse_co_allowed': 'HopperDoubleBufferMemoryWitnessTests.coCheck HopperDoubleBufferMemoryWitnessTests.sharedA (some (HopperDoubleBufferMemoryWitnessTests.firstA 2)) (some (HopperDoubleBufferMemoryWitnessTests.firstA 0)) = true',
    'full_memory_self_co_allowed': 'HopperDoubleBufferMemoryWitnessTests.coCheck HopperDoubleBufferMemoryWitnessTests.sharedA (some (HopperDoubleBufferMemoryWitnessTests.firstA 2)) (some (HopperDoubleBufferMemoryWitnessTests.firstA 2)) = true',
    'full_memory_initialization_self_co_allowed': 'HopperDoubleBufferMemoryWitnessTests.coCheck HopperDoubleBufferMemoryWitnessTests.sharedA none none = true',
    'full_memory_writer_before_initialization': 'HopperDoubleBufferMemoryWitnessTests.coCheck HopperDoubleBufferMemoryWitnessTests.sharedA (some (HopperDoubleBufferMemoryWitnessTests.firstA 2)) none = true',
    'full_memory_opposite_slot_in_co_domain': 'HopperDoubleBufferMemoryWitnessTests.coCheck HopperDoubleBufferMemoryWitnessTests.sharedA none (some (HopperDoubleBufferMemoryWitnessTests.firstA 1)) = true',
    'full_memory_read_in_co_domain': 'HopperDoubleBufferMemoryWitnessTests.coCheck HopperDoubleBufferMemoryWitnessTests.sharedA (some (HopperDoubleBufferMemoryWitnessTests.readA 0)) (some (HopperDoubleBufferMemoryWitnessTests.firstA 2)) = true',
    'full_memory_barrier_byte_has_tensor_writer': 'HopperDoubleBufferMemoryWitnessTests.coCheck ⟨.shared .zero,0⟩ none (some (HopperDoubleBufferMemoryWitnessTests.firstA 0)) = true',
    'full_memory_first_write_aliases_read_rank': 'Kernels.HopperDoubleBuffer.dataMemoryRank 3 (HopperDoubleBufferMemoryWitnessTests.firstA 0) = 26880',
    'full_memory_first_read_aliases_write_rank': 'Kernels.HopperDoubleBuffer.dataMemoryRank 3 (HopperDoubleBufferMemoryWitnessTests.readA 0) = 13056',
    'full_memory_reused_write_aliases_read_rank': 'Kernels.HopperDoubleBuffer.dataMemoryRank 3 (HopperDoubleBufferMemoryWitnessTests.firstA 2) = 67840',
    'full_memory_reused_read_aliases_write_rank': 'Kernels.HopperDoubleBuffer.dataMemoryRank 3 (HopperDoubleBufferMemoryWitnessTests.readA 2) = 41728',
    'full_memory_reused_write_drops_round_rank': 'Kernels.HopperDoubleBuffer.dataMemoryRank 3 (HopperDoubleBufferMemoryWitnessTests.firstA 2) = 13056',
    'full_memory_initial_source_rank_is_one': 'Hopper.Unified.sourceRank (Kernels.HopperDoubleBuffer.dataMemoryRank 3) none = 1',
    'full_memory_wrong_space_in_co_domain': 'HopperDoubleBufferMemoryWitnessTests.coCheck ⟨.global,16⟩ (some (HopperDoubleBufferMemoryWitnessTests.firstA 0)) (some (HopperDoubleBufferMemoryWitnessTests.firstA 2)) = true',
    'full_memory_wrong_offset_in_co_domain': 'HopperDoubleBufferMemoryWitnessTests.coCheck ⟨.shared .zero,17⟩ none (some (HopperDoubleBufferMemoryWitnessTests.firstA 0)) = true',
    'full_memory_notification_in_co_domain': 'HopperDoubleBufferMemoryWitnessTests.coCheck HopperDoubleBufferMemoryWitnessTests.sharedA none (some (.base (.tma (.notify (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferMemoryWitnessTests.a HopperDoubleBufferMemoryWitnessTests.b 3 0))))) = true',
    'full_memory_descriptor_in_co_domain': 'HopperDoubleBufferMemoryWitnessTests.coCheck HopperDoubleBufferMemoryWitnessTests.sharedA none (some (.base (.tma (.descriptor (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferMemoryWitnessTests.a HopperDoubleBufferMemoryWitnessTests.b 3 0))))) = true',
    'full_memory_input_read_in_co_domain': 'HopperDoubleBufferMemoryWitnessTests.coCheck HopperDoubleBufferMemoryWitnessTests.sharedA none (some (.base (.tma (.read (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferMemoryWitnessTests.a HopperDoubleBufferMemoryWitnessTests.b 3 0) 0)))) = true',
    'eligibility_output_footprint_is_byte': 'HopperDoubleBufferEligibilityTests.footprint 3 (HopperDoubleBufferEligibilityTests.sourceNode 3 0 35) = some (⟨.global,8192⟩,1)',
    'eligibility_native_footprint_is_word': 'HopperDoubleBufferEligibilityTests.footprint 3 (Kernels.HopperDoubleBuffer.dataNativeRead HopperDoubleBufferEligibilityTests.a HopperDoubleBufferEligibilityTests.b 3 2 (.b (15,7) 1)) = some (⟨.shared .zero,2319⟩,4)',
    'eligibility_descriptor_footprint_is_byte': 'HopperDoubleBufferEligibilityTests.footprint 3 (.base (.tma (.descriptor (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferEligibilityTests.a HopperDoubleBufferEligibilityTests.b 3 2)))) = some (⟨.global,4096⟩,1)',
    'eligibility_descriptor_address_swapped': 'HopperDoubleBufferEligibilityTests.footprint 3 (.base (.tma (.descriptor (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferEligibilityTests.a HopperDoubleBufferEligibilityTests.b 3 2)))) = some (⟨.global,4224⟩,128)',
    'eligibility_tensor_input_is_element_width': 'HopperDoubleBufferEligibilityTests.footprint 3 (.base (.tma (.read (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferEligibilityTests.a HopperDoubleBufferEligibilityTests.b 3 2) 2047))) = some (⟨.global,71679⟩,2)',
    'eligibility_reused_tensor_uses_other_slot': 'HopperDoubleBufferEligibilityTests.footprint 3 (.base (.tma (.write (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferEligibilityTests.a HopperDoubleBufferEligibilityTests.b 3 2) 2047))) = some (⟨.shared .zero,4367⟩,1)',
    'eligibility_notification_has_memory_footprint': 'HopperDoubleBufferEligibilityTests.footprint 3 (.base (.tma (.notify (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferEligibilityTests.a HopperDoubleBufferEligibilityTests.b 3 2)))) = some (⟨.shared .zero,0⟩,1)',
    'eligibility_cta_has_memory_footprint': 'HopperDoubleBufferEligibilityTests.footprint 3 (HopperDoubleBufferEligibilityTests.sourceNode 3 0 39) = some (⟨.shared .zero,0⟩,1)',
    'eligibility_absent_nonbulk_has_footprint': 'HopperDoubleBufferEligibilityTests.footprint 3 (.base (.copyRead ⟨(Kernels.HopperDoubleBuffer.ctx 3 0).id,6⟩)) = some (⟨.global,65536⟩,16)',
    'eligibility_unaligned_output_allowed': 'HopperDoubleBufferEligibilityTests.regionAllowed ⟨.global,8193⟩ 4 = true',
    'eligibility_output_past_end_allowed': 'HopperDoubleBufferEligibilityTests.regionAllowed ⟨.global,10240⟩ 4 = true',
    'eligibility_wide_shared_allowed': 'HopperDoubleBufferEligibilityTests.regionAllowed ⟨.shared .zero,16⟩ 4 = true',
    'eligibility_input_word_allowed': 'HopperDoubleBufferEligibilityTests.regionAllowed ⟨.global,65536⟩ 4 = true',
    'eligibility_descriptor_past_end_allowed': 'HopperDoubleBufferEligibilityTests.regionAllowed ⟨.global,4225⟩ 128 = true',
    'eligibility_input_before_base_allowed': 'HopperDoubleBufferEligibilityTests.regionAllowed ⟨.global,65535⟩ 1 = true',
    'eligibility_output_byte_allowed': 'HopperDoubleBufferEligibilityTests.regionAllowed ⟨.global,8192⟩ 1 = true',
    'eligibility_current_rf_selects_initial_copy': 'HopperDoubleBufferEligibilityTests.selectedProducer 3 2 (.a (0,0) 0) = some (6,0)',
    'eligibility_current_b_rf_selects_initial_copy': 'HopperDoubleBufferEligibilityTests.selectedProducer 3 2 (.b (15,7) 1) = some (7,255)',
    'eligibility_initial_rf_selects_future_copy': 'HopperDoubleBufferEligibilityTests.selectedProducer 3 0 (.a (0,0) 0) = some (20,0)',
    'eligibility_zero_round_output_is_absent': 'HopperDoubleBufferEligibilityTests.footprint 0 (HopperDoubleBufferEligibilityTests.sourceNode 0 0 5) = none',
    'shared_phase_tma_initial_is_nonbulk': 'HopperDoubleBufferMemoryPhaseTests.nonbulkAt 3 0 6 = true',
    'shared_phase_tma_reuse_is_nonbulk': 'HopperDoubleBufferMemoryPhaseTests.nonbulkAt 3 0 20 = true',
    'shared_phase_native_is_nonbulk': 'HopperDoubleBufferMemoryPhaseTests.nonbulkAt 3 127 4 = true',
    'shared_phase_output_breaks_envelope': 'HopperDoubleBufferMemoryPhaseTests.shapeAt 3 0 35 = some false',
    'shared_phase_peer_output_absent': 'HopperDoubleBufferMemoryPhaseTests.shapeAt 3 127 23 = none',
    'shared_phase_reused_a_uses_opposite_slot': 'HopperDoubleBufferMemoryPhaseTests.copyDestination 3 2 true 0 = some 2320',
    'shared_phase_a_last_byte_overlaps_b': 'HopperDoubleBufferMemoryPhaseTests.copyDestination 3 2 true 2047 = some 2064',
    'shared_phase_a_end_offset_is_valid': 'HopperDoubleBufferMemoryPhaseTests.copyDestination 3 2 true 2048 = some 2064',
    'shared_phase_b_starts_at_a': 'HopperDoubleBufferMemoryPhaseTests.copyDestination 3 2 false 0 = some 16',
    'shared_phase_b_last_byte_overlaps_next_slot': 'HopperDoubleBufferMemoryPhaseTests.copyDestination 3 2 false 255 = some 2320',
    'shared_phase_b_end_offset_is_valid': 'HopperDoubleBufferMemoryPhaseTests.copyDestination 3 2 false 256 = some 2320',
    'shared_phase_opposite_a_aliases_first_slot': 'HopperDoubleBufferMemoryPhaseTests.copyDestination 3 1 true 0 = some 16',
    'shared_phase_opposite_b_aliases_first_slot': 'HopperDoubleBufferMemoryPhaseTests.copyDestination 3 1 false 255 = some 2319',
    'shared_phase_zero_path_has_tma': '(HopperDoubleBufferMemoryPhaseTests.copyDestination 0 0 true 0).isSome = true',
    'shared_phase_reuse_changes_physical_address': 'HopperDoubleBufferMemoryPhaseTests.addressAt 3 0 (.a (0,0) 0) ≠ HopperDoubleBufferMemoryPhaseTests.addressAt 3 2 (.a (0,0) 0)',
    'shared_phase_operand_regions_overlap': 'HopperDoubleBufferMemoryPhaseTests.addressAt 3 2 (.a (63,15) 1) = HopperDoubleBufferMemoryPhaseTests.addressAt 3 2 (.b (0,0) 0)',
    'shared_phase_native_breaks_envelope': 'HopperDoubleBufferMemoryPhaseTests.shapeAt 3 0 13 = some false',
    'shared_phase_generic_shared_store_allowed': 'Kernels.HopperDoubleBuffer.memoryShape (.ampere (.ordinary (.write ⟨.shared .zero,16⟩ []))) = true',
    'shared_phase_generic_shared_load_allowed': 'Kernels.HopperDoubleBuffer.memoryShape (.ampere (.ordinary (.read ⟨.shared .zero,16⟩ []))) = true',
    'shared_phase_absolute_a_address_is_byte_offset': '(HopperDoubleBufferMemoryPhaseTests.copyDestination 3 2 true 2063).isSome = true',
    'repeat_native_three_rounds_have_eight_ops': '(Kernels.HopperDoubleBuffer.dataCompleteTrace HopperDoubleBufferNativeControlTests.a HopperDoubleBufferNativeControlTests.b 3 0).nativeSchedule.length = 8',
    'repeat_native_zero_rounds_have_native_ops': '(Kernels.HopperDoubleBuffer.dataCompleteTrace HopperDoubleBufferNativeControlTests.a HopperDoubleBufferNativeControlTests.b 0 0).nativeSchedule.length = 4',
    'repeat_native_final_signature_uses_old_group': 'HopperDoubleBufferNativeControlTests.signatureAt 3 2 127 3 = some (Kernels.HopperDoubleBuffer.dataNativeSignature 0 3)',
    'repeat_native_twice_reused_sequence_wraps': '(HopperDoubleBufferNativeControlTests.signatureAt 5 4 0 1).map (fun s => s.mark.sequence) = some 1',
    'repeat_native_same_warp_fence_fails': 'HopperDoubleBufferNativeControlTests.syncMetadata 3 0 0 0 0 31 0 = false',
    'repeat_native_second_warp_mma_fails': 'HopperDoubleBufferNativeControlTests.syncMetadata 3 1 32 1 1 63 1 = false',
    'repeat_native_final_warp_wait_fails': 'HopperDoubleBufferNativeControlTests.syncMetadata 5 4 96 3 4 127 3 = false',
    'repeat_native_cross_warp_syncs': 'HopperDoubleBufferNativeControlTests.syncMetadata 3 0 0 0 0 32 0 = true',
    'repeat_native_cross_round_syncs': 'HopperDoubleBufferNativeControlTests.syncMetadata 3 0 0 1 2 31 1 = true',
    'repeat_native_cross_instruction_syncs': 'HopperDoubleBufferNativeControlTests.syncMetadata 3 1 0 0 1 31 1 = true',
    'repeat_native_zero_path_has_signature': '(HopperDoubleBufferNativeControlTests.signatureAt 0 0 0 0).isSome = true',
    'repeat_native_short_schedule_matches': 'HopperDoubleBufferNativeControlTests.participantMetadata 3 0 2 31 31 = true',
    'repeat_native_full_schedule_mismatches': 'HopperDoubleBufferNativeControlTests.participantMetadata 5 0 5 127 127 = false',
    'repeat_native_final_fence_keeps_unshifted_tick': 'Kernels.HopperDoubleBuffer.nativeTick 3 (Kernels.HopperDoubleBuffer.dataNativeId HopperDoubleBufferNativeControlTests.a HopperDoubleBufferNativeControlTests.b 3 2 0 0) = 29',
    'repeat_native_final_peer_wait_keeps_short_stride': 'Kernels.HopperDoubleBuffer.nativeTick 3 (Kernels.HopperDoubleBuffer.dataNativeId HopperDoubleBufferNativeControlTests.a HopperDoubleBufferNativeControlTests.b 3 2 127 3) = 31',
    'repeat_native_arrival_uses_lane_return_offset': 'Kernels.HopperDoubleBuffer.dataNativeControlRank 3 (.arrival (Kernels.HopperDoubleBuffer.dataNativeId HopperDoubleBufferNativeControlTests.a HopperDoubleBufferNativeControlTests.b 3 0 31 1)) = 26685',
    'repeat_native_operand_aliases_source_issue': 'Kernels.HopperDoubleBuffer.dataNativeControlRank 3 (.operand (Kernels.HopperDoubleBuffer.dataNativeId HopperDoubleBufferNativeControlTests.a HopperDoubleBufferNativeControlTests.b 3 0 0 1) (.a (0,0) 0)) = 26624',
    'repeat_native_wait_aliases_operand': 'Kernels.HopperDoubleBuffer.dataNativeControlRank 3 (.base (.source (Kernels.HopperDoubleBuffer.dataNativeId HopperDoubleBufferNativeControlTests.a HopperDoubleBufferNativeControlTests.b 3 0 0 3))) = 26880',
    'repeat_native_highest_lane_return_aliases_operand': 'Kernels.HopperDoubleBuffer.dataNativeControlRank 5 (.base (.source (Kernels.HopperDoubleBuffer.dataNativeId HopperDoubleBufferNativeControlTests.a HopperDoubleBufferNativeControlTests.b 5 4 127 1))) = 108800',
    'repeat_native_last_operand_drops_reserved_gap': 'Kernels.HopperDoubleBuffer.dataNativeControlRank 5 (.operand (Kernels.HopperDoubleBuffer.dataNativeId HopperDoubleBufferNativeControlTests.a HopperDoubleBufferNativeControlTests.b 5 4 127 1) (.b (15,7) 1)) = 108798',
    'native_first_wait_leaves_group_pending': 'HopperDoubleBufferNativePublicationTests.waitMeta 3 0 15 = some (3,1,1,0,0,10)',
    'native_middle_wait_restarts_group': 'HopperDoubleBufferNativePublicationTests.waitMeta 3 0 25 = some (7,1,0,0,1,17)',
    'native_final_wait_keeps_prefetch_query': 'HopperDoubleBufferNativePublicationTests.waitMeta 3 0 32 = some (11,3,0,2,3,24)',
    'native_peer_uses_producer_query': 'HopperDoubleBufferNativePublicationTests.waitMeta 3 127 20 = some (11,3,0,2,3,20)',
    'native_twice_reused_group_wraps': 'HopperDoubleBufferNativePublicationTests.waitMeta 5 0 52 = some (3,1,0,0,1,34)',
    'native_twice_reused_peer_keeps_old_frontier': 'HopperDoubleBufferNativePublicationTests.waitMeta 5 127 34 = some (19,5,0,0,1,14)',
    'native_single_tile_executes_prefetch': 'HopperDoubleBufferNativePublicationTests.waitMeta 1 0 12 = some (3,1,0,0,1,10)',
    'native_cta_arrival_completes_wgmma': '(HopperDoubleBufferNativePublicationTests.waitMeta 3 0 33).isSome = true',
    'native_peer_cta_completes_wgmma': '(HopperDoubleBufferNativePublicationTests.waitMeta 3 127 21).isSome = true',
    'native_mbarrier_completes_wgmma': '(HopperDoubleBufferNativePublicationTests.waitMeta 3 0 28).isSome = true',
    'native_commit_completes_wgmma': '(HopperDoubleBufferNativePublicationTests.waitMeta 3 0 31).isSome = true',
    'native_zero_tile_has_native_wait': '(HopperDoubleBufferNativePublicationTests.waitMeta 0 0 9).isSome = true',
    'native_reused_a_uses_initial_issue': 'HopperDoubleBufferNativePublicationTests.producerMeta 3 2 (.a (63,15) 1) = some (6,2047)',
    'native_reused_b_uses_initial_issue': 'HopperDoubleBufferNativePublicationTests.producerMeta 3 2 (.b (15,7) 1) = some (7,255)',
    'native_a_offset_drops_element_byte': 'HopperDoubleBufferNativePublicationTests.producerMeta 3 2 (.a (63,15) 1) = some (20,2046)',
    'native_b_offset_drops_element_byte': 'HopperDoubleBufferNativePublicationTests.producerMeta 3 2 (.b (15,7) 1) = some (21,254)',
    'native_twice_reused_a_uses_prior_issue': 'HopperDoubleBufferNativePublicationTests.producerMeta 5 4 (.a (0,0) 0) = some (20,0)',
    'native_alternate_slot_aliases_a': 'HopperDoubleBufferNativePublicationTests.operandAddress 3 1 (.a (0,0) 0) = 16',
    'native_reused_slot_is_alternate_a': 'HopperDoubleBufferNativePublicationTests.operandAddress 3 2 (.a (63,15) 1) = 4367',
    'native_reused_slot_is_alternate_b': 'HopperDoubleBufferNativePublicationTests.operandAddress 3 2 (.b (15,7) 1) = 4623',
    'control_final_cta_uses_prior_generation': 'HopperDoubleBufferControlAdmissionTests.tagAt 3 0 33 true = some (2,1)',
    'control_peer_final_cta_uses_initial_generation': 'HopperDoubleBufferControlAdmissionTests.tagAt 3 127 22 false = some (2,0)',
    'control_second_reuse_wraps_cta_generation': 'HopperDoubleBufferControlAdmissionTests.tagAt 5 0 53 true = some (2,0)',
    'control_output_cta_counts_reuse_generations': 'HopperDoubleBufferControlAdmissionTests.tagAt 3 0 39 true = some (1,3)',
    'control_zero_tile_skips_output_cta': 'HopperDoubleBufferControlAdmissionTests.tagAt 0 0 9 true = none',
    'control_return_is_arrival': 'HopperDoubleBufferControlAdmissionTests.tagAt 3 0 34 true = some (2,2)',
    'control_wrong_generation_matches': 'HopperDoubleBufferControlAdmissionTests.ctaEdge 3 0 33 127 8',
    'control_wrong_barrier_matches': 'HopperDoubleBufferControlAdmissionTests.ctaEdge 3 0 39 127 1',
    'control_actual_cross_lane_edge_missing': '¬HopperDoubleBufferControlAdmissionTests.ctaEdge 3 0 33 127 22',
    'control_mbarrier_init_is_cta_arrival': 'HopperDoubleBufferControlAdmissionTests.tagAt 3 0 0 true = some (0,0)',
    'control_producer_gap_starts_too_late': 'Kernels.HopperDoubleBuffer.producerThreshold 3 = 32',
    'control_producer_omitted_prefetch_is_not_shifted': 'Kernels.HopperDoubleBuffer.producerTick 3 29 = 29',
    'control_peer_events_use_raw_serial': 'Kernels.HopperDoubleBuffer.peerTick 3 17 = 17',
    'control_zero_producer_tail_uses_raw_serial': 'Kernels.HopperDoubleBuffer.producerTick 0 9 = 9',
    'control_zero_peer_tail_uses_raw_serial': 'Kernels.HopperDoubleBuffer.peerTick 0 6 = 6',
    'control_last_lane_arrival_drops_lane_offset': 'Kernels.HopperDoubleBuffer.sourceControlRank 3 (Kernels.HopperDoubleBuffer.reuseCtaId HopperDoubleBufferControlAdmissionTests.a HopperDoubleBufferControlAdmissionTests.b 3 2 127 true) = 36864',
    'control_final_return_uses_raw_serial_rank': 'Kernels.HopperDoubleBuffer.sourceControlRank 3 (Kernels.HopperDoubleBuffer.reuseCtaId HopperDoubleBufferControlAdmissionTests.a HopperDoubleBufferControlAdmissionTests.b 3 2 0 false) = 34816',
    'control_tma_write_aliases_read_rank': 'Kernels.HopperDoubleBuffer.controlRank 3 (.write (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferControlAdmissionTests.a HopperDoubleBufferControlAdmissionTests.b 3 0) 0) = 6400',
    'control_tma_notify_aliases_write_rank': 'Kernels.HopperDoubleBuffer.controlRank 3 (.notify (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferControlAdmissionTests.a HopperDoubleBufferControlAdmissionTests.b 3 0)) = 6528',
    'control_wait_precedes_its_current_notification': 'Kernels.HopperDoubleBuffer.sourceControlRank 3 (Kernels.HopperDoubleBuffer.dataWaitId HopperDoubleBufferControlAdmissionTests.a HopperDoubleBufferControlAdmissionTests.b 3 2 127) < Kernels.HopperDoubleBuffer.controlRank 3 (.notify (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferControlAdmissionTests.a HopperDoubleBufferControlAdmissionTests.b 3 2))',
    'resource_missing_a_preserves_length': 'HopperDoubleBufferResourceAdmissionTests.missingA.length = 264',
    'resource_ghost_preserves_length': 'HopperDoubleBufferResourceAdmissionTests.ghostHistory.length = 264',
    'resource_missing_a_protocol_succeeds': 'Hopper.Mbarrier.run none (HopperDoubleBufferResourceAdmissionTests.operations HopperDoubleBufferResourceAdmissionTests.missingA) = some none',
    'resource_ghost_protocol_is_sufficient_rejection': 'Hopper.Mbarrier.run none (HopperDoubleBufferResourceAdmissionTests.operations HopperDoubleBufferResourceAdmissionTests.ghostHistory) = none',
    'resource_ghost_copy_uses_initial_a_source': 'HopperDoubleBufferResourceAdmissionTests.ghostCopy.issue.serial = 6',
    'resource_missing_a_still_contains_notice': '(Hopper.Tma.Entry.mk (.notification (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferResourceAdmissionTests.a HopperDoubleBufferResourceAdmissionTests.b 3 0)) (.completeTx 2048)) ∈ HopperDoubleBufferResourceAdmissionTests.missingA',
    'resource_missing_a_first_notice_is_a': 'HopperDoubleBufferResourceAdmissionTests.originAt HopperDoubleBufferResourceAdmissionTests.missingA 2 = some (.notification (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferResourceAdmissionTests.a HopperDoubleBufferResourceAdmissionTests.b 3 0))',
    'resource_ghost_origin_is_real_a': 'HopperDoubleBufferResourceAdmissionTests.originAt HopperDoubleBufferResourceAdmissionTests.ghostHistory 1 = some (.notification (Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferResourceAdmissionTests.a HopperDoubleBufferResourceAdmissionTests.b 3 0))',
    'resource_data_address_has_phase_history': '(Kernels.HopperDoubleBuffer.dataHistories HopperDoubleBufferResourceAdmissionTests.a HopperDoubleBufferResourceAdmissionTests.b 3 ⟨.shared .zero,16⟩).length = 264',
    'resource_other_cta_has_phase_history': '(Kernels.HopperDoubleBuffer.dataHistories HopperDoubleBufferResourceAdmissionTests.a HopperDoubleBufferResourceAdmissionTests.b 3 ⟨.shared ⟨1,0,0⟩,0⟩).length = 264',
    'resource_unused_stage_invents_phase': '(Kernels.HopperDoubleBuffer.dataHistories HopperDoubleBufferResourceAdmissionTests.a HopperDoubleBufferResourceAdmissionTests.b 1 (Kernels.HopperDoubleBuffer.dataGate 1)).length = 133',
    'resource_proxy_fence_is_mbarrier': 'Kernels.HopperDoubleBuffer.isResourceEvent (.base (.proxyFenceAsyncShared .zero)) = true',
    'resource_cta_arrival_is_mbarrier': 'Kernels.HopperDoubleBuffer.isResourceEvent (.base (.ampere (.ordinary (.barrierArrival 2 0)))) = true',
    'resource_wgmma_fence_is_mbarrier': 'Kernels.HopperDoubleBuffer.isResourceEvent (.fence ⟨77,1,0⟩) = true',
    'resource_tma_issue_is_ignored': 'Kernels.HopperDoubleBuffer.isResourceEvent (.base (.tmaIssue (Kernels.HopperDoubleBuffer.dataCopyA HopperDoubleBufferResourceAdmissionTests.a 3 2))) = false',
    'resource_unknown_tensor_map_is_present': '(Kernels.HopperDoubleBuffer.dataMaps 3 4352).isSome = true',
    'history_rank_second_init_uses_source_serial': 'Kernels.HopperDoubleBuffer.sourcePosition 3 1 0 1 = 1',
    'history_rank_reused_expect_resets': 'HopperDoubleBufferResourceOrderTests.rankAt 3 0 132 = some 1',
    'history_rank_reused_a_resets': 'HopperDoubleBufferResourceOrderTests.rankAt 3 0 133 = some 2',
    'history_rank_reused_b_aliases_a': 'HopperDoubleBufferResourceOrderTests.rankAt 3 0 134 = some 133',
    'history_rank_reused_wait_resets': 'HopperDoubleBufferResourceOrderTests.rankAt 3 0 135 = some 4',
    'history_rank_last_peer_uses_producer_position': 'HopperDoubleBufferResourceOrderTests.rankAt 3 0 262 = some 135',
    'history_rank_invalidation_uses_source_serial': 'HopperDoubleBufferResourceOrderTests.rankAt 3 0 263 = some 41',
    'history_rank_twice_reused_a_resets': 'HopperDoubleBufferResourceOrderTests.rankAt 5 0 264 = some 133',
    'history_rank_second_slot_wait_uses_serial': 'HopperDoubleBufferResourceOrderTests.rankAt 3 1 4 = some 18',
    'history_rank_zero_invalidation_uses_serial': 'HopperDoubleBufferResourceOrderTests.rankAt 0 0 1 = some 11',
    'history_serial_producer_uses_peer_stride': 'Kernels.HopperDoubleBuffer.waitSerial 4 0 = 30',
    'history_serial_peer_uses_producer_stride': 'Kernels.HopperDoubleBuffer.waitSerial 4 127 = 48',
    'history_serial_expect_uses_copy_serial': 'Kernels.HopperDoubleBuffer.expectSerial 4 = 40',
    'history_serial_b_aliases_a': 'Kernels.HopperDoubleBuffer.copyBSerial 4 = 40',
    'history_serial_invalidation_drops_last_phase': 'Kernels.HopperDoubleBuffer.invalSerial 5 0 = 51',
    'history_duplicate_initialization_unique': '((HopperDoubleBufferResourceOrderTests.duplicated 0 0).map Hopper.Tma.Entry.origin).Nodup',
    'history_reverse_zero_preserves_source_order': 'Hopper.Tma.SourceOrder (HopperDoubleBufferResourceOrderTests.history 0 0).reverse',
    'history_omitted_invalidation_is_exhaustive': '(HopperDoubleBufferResourceOrderTests.omittedZero).Perm (HopperDoubleBufferResourceOrderTests.history 0 0)',
    'history_initial_a_points_to_b_notice': 'HopperDoubleBufferResourceTests.observed 3 0 2 4 = some (7,8)',
    'history_initial_b_uses_producer_wait_for_peer': 'HopperDoubleBufferResourceTests.observed 3 0 3 131 = some (7,8)',
    'history_reused_a_repeats_old_copy': 'HopperDoubleBufferResourceTests.observed 3 0 133 135 = some (6,28)',
    'history_reused_b_repeats_old_copy': 'HopperDoubleBufferResourceTests.observed 3 0 134 262 = some (7,16)',
    'history_old_a_confirms_reuse': 'HopperDoubleBufferResourceTests.observed 3 0 2 135 = some (6,28)',
    'history_old_b_confirms_reuse': 'HopperDoubleBufferResourceTests.observed 3 0 3 262 = some (7,16)',
    'history_parity_wrap_revives_a': 'HopperDoubleBufferResourceTests.observed 5 0 2 266 = some (6,48)',
    'history_parity_wrap_revives_b': 'HopperDoubleBufferResourceTests.observed 5 0 3 393 = some (7,30)',
    'history_future_notice_confirms_prior_wait': 'HopperDoubleBufferResourceTests.observed 3 0 133 4 = some (20,8)',
    'history_arrival_invents_notification': 'HopperDoubleBufferResourceTests.observed 3 0 1 4 = some (6,8)',
    'history_arrival_invents_successful_wait': 'HopperDoubleBufferResourceTests.observed 3 0 2 1 = some (6,5)',
    'history_a_notification_is_already_next_phase': 'HopperDoubleBufferResourceTests.stamp 3 0 2 = some ⟨1,1⟩',
    'history_b_notification_is_already_next_phase': 'HopperDoubleBufferResourceTests.stamp 3 0 3 = some ⟨1,1⟩',
    'history_reused_wait_retains_previous_phase': 'HopperDoubleBufferResourceTests.stamp 3 0 135 = some ⟨1,1⟩',
    'history_slot_reuse_reinitializes_lifetime': 'HopperDoubleBufferResourceTests.stamp 5 0 393 = some ⟨3,3⟩',
    'history_parity_wrap_resets_absolute_phase': 'HopperDoubleBufferResourceTests.stamp 5 0 393 = some ⟨1,1⟩',
    'history_omits_one_stage_phase': '(HopperDoubleBufferResourceTests.history 3 0).length = 133',
    'history_zero_tile_invents_phase': '(HopperDoubleBufferResourceTests.history 0 0).length = 133',
    'history_final_invalidation_uses_other_source': 'HopperDoubleBufferResourceTests.originAt 3 0 263 = some (.source ⟨(Kernels.HopperDoubleBuffer.ctx 3 0).id,42⟩)',
    'history_peer_wait_uses_wrong_tile_source': 'HopperDoubleBufferResourceTests.originAt 3 0 262 = some (.source ⟨(Kernels.HopperDoubleBuffer.ctx 3 127).id,2⟩)',
    'indexed_final_mma_retains_prefetch_gap': 'HopperDoubleBufferIndexTests.mmaAt 3 0 33 = some ⟨77,9,2,2,19,68720001025,68720001153⟩',
    'indexed_final_mma_uses_second_stage': 'HopperDoubleBufferIndexTests.mmaAt 3 0 30 = some ⟨77,9,2,2,19,68720001169,68720001297⟩',
    'indexed_final_mma_resets_sequence': 'HopperDoubleBufferIndexTests.mmaAt 3 0 30 = some ⟨77,1,2,2,19,68720001025,68720001153⟩',
    'indexed_final_mma_reuses_group': 'HopperDoubleBufferIndexTests.mmaAt 3 0 30 = some ⟨77,9,2,1,19,68720001025,68720001153⟩',
    'indexed_peer_uses_producer_index': 'HopperDoubleBufferIndexTests.mmaAt 3 127 30 = some ⟨77,9,2,2,7,68720001025,68720001153⟩',
    'indexed_peer_uses_producer_query': 'HopperDoubleBufferIndexTests.mmaAt 3 127 18 = some ⟨77,9,2,2,19,68720001025,68720001153⟩',
    'indexed_initial_copy_uses_second_slot': 'HopperDoubleBufferIndexTests.copyAt 3 6 = some ⟨65536,2320,8,0,0,2048⟩',
    'indexed_second_copy_repeats_first_slot': 'HopperDoubleBufferIndexTests.copyAt 3 10 = some ⟨65536,16,0,5,8,2048⟩',
    'indexed_reused_copy_retains_second_slot': 'HopperDoubleBufferIndexTests.copyAt 3 20 = some ⟨65536,2320,8,12,16,2048⟩',
    'indexed_reused_copy_repeats_tile_zero': 'HopperDoubleBufferIndexTests.copyAt 3 20 = some ⟨65536,16,0,0,0,2048⟩',
    'indexed_b_copy_uses_a_stride': 'HopperDoubleBufferIndexTests.copyAt 3 21 = some ⟨71680,2064,0,14,16,256⟩',
    'indexed_b_copy_uses_a_byte_count': 'HopperDoubleBufferIndexTests.copyAt 3 21 = some ⟨71680,2064,0,14,2,2048⟩',
    'indexed_twice_reused_copy_retains_previous_tile': 'HopperDoubleBufferIndexTests.copyAt 5 40 = some ⟨65536,16,0,26,16,2048⟩',
    'indexed_reused_wait_has_old_parity': 'HopperDoubleBufferIndexTests.waitAt 3 0 28 = some (0,0,true)',
    'indexed_reused_wait_uses_other_barrier': 'HopperDoubleBufferIndexTests.waitAt 3 0 28 = some (8,1,true)',
    'indexed_peer_wait_uses_producer_index': 'HopperDoubleBufferIndexTests.waitAt 3 127 28 = some (0,1,true)',
    'indexed_zero_tile_issues_copy': 'HopperDoubleBufferIndexTests.copyAt 0 6 = some ⟨65536,16,0,0,0,2048⟩',
    'indexed_same_slot_reuses_copy_identity': 'Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferIndexTests.a HopperDoubleBufferIndexTests.b 3 0 = Kernels.HopperDoubleBuffer.dataCopyAId HopperDoubleBufferIndexTests.a HopperDoubleBufferIndexTests.b 3 2',
    'data_native_final_query_is_prefetch_stride': 'Kernels.HopperDoubleBuffer.nativeQuery 3 2 true = 23',
    'data_native_final_query_selects_prior_tile': 'Kernels.HopperDoubleBuffer.nativeTile 3 true 19 = 1',
    'data_native_consumer_query_selects_first_tile': 'Kernels.HopperDoubleBuffer.nativeTile 3 false 7 = 0',
    'data_prefetch_a_payload_repeats_tile_one': 'Kernels.HopperDoubleBuffer.aPayloadTile 13 = 1',
    'data_prefetch_b_payload_repeats_tile_one': 'Kernels.HopperDoubleBuffer.bPayloadTile 15 = 1',
    'data_initial_payload_skips_tile_zero': 'Kernels.HopperDoubleBuffer.aPayloadTile 1 = 1',
    'data_old_fixed_b_base_is_disjoint_at_100': '65536+2048*100 ≤ 131072',
    'data_three_tile_b_uses_old_fixed_base': 'Kernels.HopperDoubleBuffer.dataBBase 3 = 131072',
    'data_100_tile_b_uses_old_fixed_base': 'Kernels.HopperDoubleBuffer.dataBBase 100 = 131072',
    'data_b_base_is_unaligned': 'Kernels.HopperDoubleBuffer.dataBBase 100 % 16 = 1',
    'data_b_descriptor_uses_old_fixed_base': '(Kernels.HopperDoubleBuffer.dataDescriptor 100 2).base = 131072',
    'data_prefetch_b_descriptor_uses_a_base': '(Kernels.HopperDoubleBuffer.dataDescriptor 3 7).base = 65536',
    'data_nonuniform_producer_omits_transfers': 'HopperDoubleBufferDataTests.metadata 3 0 = some ⟨100,13,3,3,0,3,true⟩',
    'data_nonuniform_peer_adds_transfer_queries': 'HopperDoubleBufferDataTests.metadata 3 127 = some ⟨100,21,3,3,0,3,true⟩',
    'data_nonuniform_retains_pending_call': 'HopperDoubleBufferDataTests.metadata 3 0 = some ⟨100,21,3,3,1,3,true⟩',
    'data_nonuniform_drops_call_history': 'HopperDoubleBufferDataTests.metadata 3 0 = some ⟨100,21,3,3,0,1,true⟩',
    'data_nonuniform_zero_tile_does_not_return': 'HopperDoubleBufferDataTests.metadata 0 0 = some ⟨85,0,0,0,0,0,false⟩',
    'data_final_captured_call_uses_previous_group': '(Kernels.HopperDoubleBuffer.dataIterationCall HopperDoubleBufferDataTests.a HopperDoubleBufferDataTests.b 3 2 0).group = 1',
    'data_final_captured_call_uses_previous_query': '(Kernels.HopperDoubleBuffer.dataIterationCall HopperDoubleBufferDataTests.a HopperDoubleBufferDataTests.b 3 2 0).query = 16',
    'data_peer_captured_call_uses_producer_query': '(Kernels.HopperDoubleBuffer.dataIterationCall HopperDoubleBufferDataTests.a HopperDoubleBufferDataTests.b 3 2 127).query = 19',
    'complete_source_is_still_output_entry': 'HopperDoubleBufferCompleteTests.metadata 6 0 = some ⟨85,42,6,6,0,6,false⟩',
    'complete_source_stores_consume_queries': 'HopperDoubleBufferCompleteTests.metadata 6 0 = some ⟨100,46,6,6,0,6,true⟩',
    'complete_source_discards_call_history': 'HopperDoubleBufferCompleteTests.metadata 6 0 = some ⟨100,42,6,6,0,1,true⟩',
    'complete_source_returns_with_pending_call': 'HopperDoubleBufferCompleteTests.metadata 6 0 = some ⟨100,42,6,6,1,6,true⟩',
    'complete_source_zero_tile_does_not_return': 'HopperDoubleBufferCompleteTests.metadata 0 0 = some ⟨85,0,0,0,0,0,false⟩',
    'complete_source_invalidates_only_first_barrier': 'HopperDoubleBufferCompleteTests.invalidated 6 0 = some [0]',
    'complete_source_peer_invalidates_barriers': 'HopperDoubleBufferCompleteTests.invalidated 6 127 = some [0,8]',
    'complete_source_zero_tile_skips_invalidation': 'HopperDoubleBufferCompleteTests.invalidated 0 0 = some []',
    'complete_source_writes_eight_bytes_per_value': 'HopperDoubleBufferCompleteTests.writes 6 0 = some [(8192,8),(8196,8),(8448,8),(8452,8)]',
    'complete_source_uses_half_row_stride': 'HopperDoubleBufferCompleteTests.writes 6 0 = some [(8192,4),(8196,4),(8320,4),(8324,4)]',
    'complete_source_aliases_four_outputs': 'HopperDoubleBufferCompleteTests.writes 6 0 = some [(8192,4),(8192,4),(8192,4),(8192,4)]',
    'complete_source_last_word_starts_outside_allocation': 'HopperDoubleBufferCompleteTests.writes 6 127 = some [(9976,4),(9980,4),(10232,4),(10240,4)]',
    'complete_source_interior_lane_uses_wrong_row': 'HopperDoubleBufferCompleteTests.writes 6 43 = some [(8760,4),(8764,4),(9016,4),(9020,4)]',
    'complete_source_zero_tile_omits_output_stores': 'HopperDoubleBufferCompleteTests.writes 0 127 = some []',
    'complete_source_symbolic_f32_is_bits_only': 'HopperDoubleBufferCompleteTests.byteTags 6 127 = some (List.replicate 4 [(0,0),(0,0),(0,0),(0,0)])',
    'complete_source_omits_return_fuel': 'Kernels.HopperDoubleBuffer.completeSteps 6 0 = 243',
    'complete_source_zero_tile_omits_output_fuel': 'Kernels.HopperDoubleBuffer.completeSteps 0 0 = 35',
    'complete_source_has_sixteen_store_events': '(HopperDoubleBufferCompleteTests.writes 6 0).map List.length = some 16',
    'complete_source_last_byte_exceeds_allocation': 'Kernels.HopperDoubleBuffer.outputByteAddress (127,3) 3 = 10243',
    'complete_source_distinct_owners_alias': 'Kernels.HopperDoubleBuffer.outputByteAddress (0,0) 0 = Kernels.HopperDoubleBuffer.outputByteAddress (1,0) 0',
    'full_loop_producer_drops_prefetch_queries': 'HopperDoubleBufferLoopTests.metadata 6 true = some ⟨85,22,6,6,0,6,some 6,some 0,some 1,some 1⟩',
    'full_loop_consumer_adds_prefetch_queries': 'HopperDoubleBufferLoopTests.metadata 6 false = some ⟨85,42,6,6,0,6,some 6,some 0,some 1,some 1⟩',
    'full_loop_keeps_pending_call': 'HopperDoubleBufferLoopTests.metadata 6 true = some ⟨85,42,6,6,1,6,some 6,some 0,some 1,some 1⟩',
    'full_loop_drops_prior_calls': 'HopperDoubleBufferLoopTests.metadata 6 true = some ⟨85,42,6,6,0,1,some 6,some 0,some 1,some 1⟩',
    'full_loop_phase_zero_never_wraps': 'HopperDoubleBufferLoopTests.metadata 7 true = some ⟨85,49,7,7,0,7,some 7,some 1,some 1,some 1⟩',
    'full_loop_prefetches_final_tile': 'Kernels.HopperDoubleBuffer.loopPrefetchCount 0 7 true 7 = 7',
    'full_loop_queries_ignore_retry_schedule': 'Kernels.HopperDoubleBuffer.loopQuery 0 7 true HopperDoubleBufferLoopTests.varyingRetries 4 7 = 49',
    'full_loop_consumer_queries_ignore_retries': 'Kernels.HopperDoubleBuffer.loopQuery 0 7 false HopperDoubleBufferLoopTests.varyingRetries 0 7 = 21',
    'full_loop_successive_wait_windows_overlap': 'Kernels.HopperDoubleBuffer.loopQuery 0 7 true HopperDoubleBufferLoopTests.varyingRetries 4 1 = 4',
    'full_kernel_entry_misses_initial_transfers': 'HopperDoubleBufferKernelLoopTests.transferQueries 6 0 = some [5,7,12,14,19,21,26,28,33,35]',
    'full_kernel_peer_initializes_shared_barriers': 'HopperDoubleBufferKernelLoopTests.initialized 6 127 = some [0,8]',
    'full_kernel_zero_tile_skips_barrier_initialization': 'HopperDoubleBufferKernelLoopTests.initialized 0 0 = some []',
    'full_kernel_zero_tile_issues_tma': 'HopperDoubleBufferKernelLoopTests.transferQueries 0 0 = some [0,2]',
    'full_kernel_output_entry_is_done': '(HopperDoubleBufferKernelLoopTests.metadata 6 0).map (fun m => m.done) = some true',
    'full_kernel_zero_output_entry_is_done': '(HopperDoubleBufferKernelLoopTests.metadata 0 0).map (fun m => m.done) = some true',
    'full_kernel_interior_lane_is_producer': '(HopperDoubleBufferKernelLoopTests.metadata 6 43).map (fun m => m.leader) = some (some 1)',
    'full_kernel_interior_lane_loses_z': '(HopperDoubleBufferKernelLoopTests.metadata 6 43).map (fun m => m.z) = some (some 0)',
    'full_kernel_output_entry_counter_is_old_tile': '(HopperDoubleBufferKernelLoopTests.metadata 6 0).map (fun m => m.tile) = some (some 5)',
    'full_kernel_output_entry_fuel_includes_return': 'Kernels.HopperDoubleBuffer.kernelLoopSteps 6 0 = 259',
    'full_kernel_multidimensional_second_slice_is_leader': 'Kernels.HopperStage.leader 32 = true',
    'iteration_prefetch_overwrites_current_stage': 'HopperDoubleBufferIterationTests.transfers 0 3 2 true = some [(16,4096,8,0),(2064,4224,1,0)]',
    'iteration_odd_prefetch_uses_current_stage': 'HopperDoubleBufferIterationTests.transfers 1 3 1 true = some [(2320,4096,16,8),(4368,4224,2,8)]',
    'iteration_prefetch_swaps_tensor_maps': 'HopperDoubleBufferIterationTests.transfers 0 3 2 true = some [(2320,4224,8,8),(4368,4096,1,8)]',
    'iteration_prefetch_a_uses_b_coordinate': 'HopperDoubleBufferIterationTests.transfers 0 3 2 true = some [(2320,4096,1,8),(4368,4224,1,8)]',
    'iteration_prefetch_b_uses_a_coordinate': 'HopperDoubleBufferIterationTests.transfers 0 3 2 true = some [(2320,4096,8,8),(4368,4224,8,8)]',
    'iteration_prefetch_queries_restart_from_zero': 'HopperDoubleBufferIterationTests.transferQueries 0 3 2 true = some [0,2]',
    'iteration_prefetch_queries_ignore_retries': 'HopperDoubleBufferIterationTests.transferQueries 0 3 2 true = some [8,10]',
    'iteration_prefetch_copies_share_query': 'HopperDoubleBufferIterationTests.transferQueries 0 3 2 true = some [10,10]',
    'iteration_producer_drops_transfer_queries': 'HopperDoubleBufferIterationTests.metadata 0 3 2 true = some ⟨45,12,1,1,0,1,some 1,some 1,some 1,some 0⟩',
    'iteration_consumer_consumes_transfer_queries': 'HopperDoubleBufferIterationTests.metadata 0 3 2 false = some ⟨45,16,1,1,0,1,some 1,some 1,some 1,some 0⟩',
    'iteration_reuse_wait_uses_initial_parity': 'HopperDoubleBufferIterationTests.waits 2 4 0 true = some [(0,0,true)]',
    'iteration_drops_old_call_history': 'HopperDoubleBufferIterationTests.metadata 2 4 0 true = some ⟨45,14,3,3,0,1,some 3,some 1,some 0,some 1⟩',
    'iteration_prefetch_changes_current_mma_operands': 'HopperDoubleBufferIterationTests.lastCallMetadata 0 3 2 true = some (68720001169,68720001297,0,14)',
    'iteration_odd_prefetch_changes_current_mma_operands': 'HopperDoubleBufferIterationTests.lastCallMetadata 1 3 1 true = some (68720001025,68720001153,1,13)',
    'iteration_short_a_payload_accepted': 'HopperDoubleBufferIterationTests.fault (HopperDoubleBufferIterationTests.malformed 3 2 true) 0 3 2 true = none',
    'iteration_large_b_payload_accepted': 'HopperDoubleBufferIterationTests.fault (HopperDoubleBufferIterationTests.malformed 3 2 false) 0 3 2 true = none',
    'iteration_consumer_requires_unused_payload': 'HopperDoubleBufferIterationTests.fault (HopperDoubleBufferIterationTests.malformed 3 2 true) 0 3 2 false = some (.base (.tmaPayloadSize 2048 256))',
    'iteration_last_tile_requires_unused_payload': 'HopperDoubleBufferIterationTests.fault (HopperDoubleBufferIterationTests.malformed 4 1 true) 3 4 1 true = some (.base (.tmaPayloadSize 2048 256))',
    'iteration_final_tile_reenters_loop': 'HopperDoubleBufferIterationTests.metadata 3 4 1 true = some ⟨45,11,4,4,0,4,some 4,some 0,some 0,some 0⟩',
    'iteration_failed_waits_are_erased': 'HopperDoubleBufferIterationTests.waits 0 3 2 true = some [(0,0,true)]',
    'loop_guard_producer_skips_available_tile': 'HopperDoubleBufferLoopControlTests.guardMetadata 0 3 true = some (76,13,some 1,some 1)',
    'loop_guard_consumer_issues_prefetch': 'HopperDoubleBufferLoopControlTests.guardMetadata 0 3 false = some (65,13,some 1,some 1)',
    'loop_guard_last_tile_issues_prefetch': 'HopperDoubleBufferLoopControlTests.guardMetadata 2 3 true = some (65,13,some 3,some 1)',
    'loop_guard_next_tile_does_not_increment': 'HopperDoubleBufferLoopControlTests.guardMetadata 0 3 true = some (65,13,some 0,some 1)',
    'loop_tail_final_tile_continues': 'HopperDoubleBufferLoopControlTests.tailMetadata 2 3 = some (45,13,some 3,some 1,6,2)',
    'loop_tail_does_not_toggle_stage': 'HopperDoubleBufferLoopControlTests.tailMetadata 0 3 = some (45,13,some 1,some 0,6,2)',
    'loop_tail_drops_rendezvous_events': 'HopperDoubleBufferLoopControlTests.tailMetadata 0 3 = some (45,13,some 1,some 1,6,0)',
    'loop_tail_reuses_barrier_generation': 'HopperDoubleBufferLoopControlTests.tailMetadata 0 3 = some (45,13,some 1,some 1,5,2)',
    'loop_tail_consumes_oracle_query': 'HopperDoubleBufferLoopControlTests.tailMetadata 0 3 = some (45,14,some 1,some 1,6,2)',
    'loop_counter_unbounded_nat_addition': 'HopperDoubleBufferLoopControlTests.guardMetadata 4294967295 4294967295 true = some (76,13,some 4294967296,some 0)',
    'cta_rendezvous_completes_wgmma': 'HopperDoubleBufferLoopControlTests.rendezvousMetadata = some (0,1,81)',
    'commit_completes_new_wgmma_group': 'HopperDoubleBufferLoopControlTests.computeMetadata 3 0 3 = some ⟨79,14,4,4,4,0,15⟩',
    'wait_zero_drops_historical_calls': 'HopperDoubleBufferLoopControlTests.computeMetadata 4 0 3 = some ⟨80,15,4,4,1,0,16⟩',
    'wait_zero_preserves_pending_call': 'HopperDoubleBufferLoopControlTests.computeMetadata 4 0 3 = some ⟨80,15,4,3,4,1,16⟩',
    'native_wait_does_not_consume_query': 'HopperDoubleBufferLoopControlTests.computeMetadata 4 0 3 = some ⟨80,14,4,4,4,0,16⟩',
    'native_tail_increments_group_twice': 'HopperDoubleBufferLoopControlTests.computeMetadata 9 0 3 = some ⟨45,15,5,5,4,0,16⟩',
    'native_tail_last_tile_restarts_loop': 'HopperDoubleBufferLoopControlTests.computeMetadata 9 2 3 = some ⟨45,15,4,4,4,0,16⟩',
    'double_buffer_odd_header_selects_first_barrier': '((HopperDoubleBufferControlTests.registers 1 0).bind (fun rs => rs[0]?.join)) = some 0',
    'double_buffer_reuse_header_keeps_old_parity': '((HopperDoubleBufferControlTests.registers 2 3).bind (fun rs => rs[3]?.join)) = some 0',
    'double_buffer_even_phase_fails_to_flip': '((HopperDoubleBufferControlTests.registers 2 3).bind (fun rs => rs[4]?.join)) = some 1',
    'double_buffer_even_phase_flips_peer': '((HopperDoubleBufferControlTests.registers 2 3).bind (fun rs => rs[5]?.join)) = some 0',
    'double_buffer_odd_phase_fails_to_flip': '((HopperDoubleBufferControlTests.registers 3 1).bind (fun rs => rs[5]?.join)) = some 1',
    'double_buffer_header_parity_never_wraps': '((HopperDoubleBufferControlTests.registers 4 3).bind (fun rs => rs[3]?.join)) = some 1',
    'double_buffer_retries_reset_query_origin': 'HopperDoubleBufferControlTests.pcQueries 2 3 = some (61,4)',
    'double_buffer_failed_waits_consume_no_queries': 'HopperDoubleBufferControlTests.pcQueries 2 3 = some (61,8)',
    'double_buffer_successful_test_loops': 'HopperDoubleBufferControlTests.pcQueries 2 3 = some (55,11)',
    'double_buffer_failed_waits_disappear': 'HopperDoubleBufferControlTests.waits 2 3 = some [(0,1,true)]',
    'double_buffer_odd_retry_uses_first_barrier': 'HopperDoubleBufferControlTests.waits 3 1 = some [(0,1,false),(0,1,true)]',
    'double_buffer_odd_selection_has_six_steps': 'Kernels.HopperDoubleBuffer.selectionSteps 3 = 6',
    'shift_u64_accepts_wide_count': 'ISA.InstructionTyped ShiftTests.registers [] 1 (.bin .shr 64 64 "wide" (.reg "bits") (.reg "wide"))',
    'shift_u64_accepts_pred_count': 'ISA.InstructionTyped ShiftTests.registers [] 1 (.bin .shr 64 64 "wide" (.reg "bits") (.reg "p"))',
    'shift_widening_form_accepted': 'ISA.InstructionTyped ShiftTests.registers [] 1 (.bin .shr 32 64 "wide" (.reg "word") (.imm 4))',
    'shift_top_bit_is_not_logical': 'ShiftTests.observed 32 4294967295 31 = some 4294967295',
    'shift_32_masks_count': 'ShiftTests.observed 32 4294967295 32 = some 4294967295',
    'shift_64_masks_count': 'ShiftTests.observed 64 18446744073709551615 64 = some 18446744073709551615',
    'shift_64_count_32_is_zero': 'ShiftTests.observed 64 4294967296 32 = some 0',
    'runtime_descriptor_uses_first_buffer': '(Hopper.Wgmma.MatrixDescriptor.decode (Hopper.Wgmma.encodeShared 2320)).base = 16',
    'double_buffer_reuses_next_stage': 'Kernels.HopperDoubleBuffer.stage 0 = Kernels.HopperDoubleBuffer.stage 1',
    'double_buffer_third_tile_uses_old_parity': 'Kernels.HopperDoubleBuffer.expectedParity 2 = 0',
    'double_buffer_parity_does_not_wrap': 'Kernels.HopperDoubleBuffer.expectedParity 4 = 1',
    'double_buffer_second_stage_uses_one_time': 'Kernels.HopperDoubleBuffer.uses 4 1 = 1',
    'double_buffer_last_shared_byte_drops_stage': 'Kernels.HopperDoubleBuffer.bBase 1+256 = 2320',
    'double_buffer_shared_allocation_understates_end': 'Generated.hopper_double_buffer_gemm.sharedBytes = 4608',
    'double_buffer_missing_b_can_wait': '(Hopper.Mbarrier.run (some (Kernels.HopperDoubleBuffer.readyState 0)) [.arriveExpectTx 2304,.completeTx 2048,.tryWaitParity 0 true]).isSome = true',
    'double_buffer_missing_a_can_wait': '(Hopper.Mbarrier.run (some (Kernels.HopperDoubleBuffer.readyState 0)) [.arriveExpectTx 2304,.completeTx 256,.tryWaitParity 0 true]).isSome = true',
    'double_buffer_unobserved_phase_can_restart': '(Hopper.Mbarrier.step (some (Kernels.HopperDoubleBuffer.transferredState 0)) (.arriveExpectTx 2304)).isSome = true',
    'double_buffer_stale_parity_confirms_reuse': '(Hopper.Mbarrier.step (some (Kernels.HopperDoubleBuffer.transferredState 1)) (.tryWaitParity 0 true)).isSome = true',
    'double_buffer_three_tile_groups_are_two': '(Kernels.HopperDoubleBuffer.probeTrace 3 0).final.ledger.groups = 2',
    'double_buffer_three_tile_peer_retains_pending': '(Hopper.Wgmma.pending (Kernels.HopperDoubleBuffer.probeTrace 3 1).final.ledger).length = 1',
    'native_sync_extends_to_next_warp': 'Hopper.Unified.NativeSync Kernels.HopperStage.block (Kernels.HopperStage.candidate UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB) (Kernels.HopperStage.nativeId 0 0) (Kernels.HopperStage.nativeId 32 0)',
    'native_sync_extends_to_last_warp': 'Hopper.Unified.NativeSync Kernels.HopperStage.block (Kernels.HopperStage.candidate UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB) (Kernels.HopperStage.nativeId 0 0) (Kernels.HopperStage.nativeId 127 0)',
    'native_sync_rejects_last_lane_same_warp': '¬Hopper.Unified.NativeSync Kernels.HopperStage.block (Kernels.HopperStage.candidate UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB) (Kernels.HopperStage.nativeId 0 0) (Kernels.HopperStage.nativeId 31 0)',
    'native_sync_matches_fence_and_mma': 'Hopper.Unified.NativeSync Kernels.HopperStage.block (Kernels.HopperStage.candidate UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB) (Kernels.HopperStage.nativeId 0 0) (Kernels.HopperStage.nativeId 31 1)',
    'native_sync_matches_commit_and_wait': 'Hopper.Unified.NativeSync Kernels.HopperStage.block (Kernels.HopperStage.candidate UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB) (Kernels.HopperStage.nativeId 0 2) (Kernels.HopperStage.nativeId 31 3)',
    'native_arrival_follows_own_return': 'Kernels.HopperStage.nativeControlRank (.base (.source (Kernels.HopperStage.nativeId 0 0))) < Kernels.HopperStage.nativeControlRank (.arrival (Kernels.HopperStage.nativeId 0 0))',
    'native_return_precedes_peer_arrival': 'Kernels.HopperStage.nativeControlRank (.base (.source (Kernels.HopperStage.nativeId 0 0))) < Kernels.HopperStage.nativeControlRank (.arrival (Kernels.HopperStage.nativeId 31 0))',
    'native_index_drops_fence_event': '(Kernels.HopperStage.nativeSignature 0).pc = 29',
    'native_index_wait_has_mma_sequence': '(Kernels.HopperStage.nativeSignature 3).mark.sequence = 1',
    'native_cycle_schedule_has_no_fence': '(HopperCollectiveCycleTests.trace 0).nativeSchedule.length = 0',
    'native_cycle_same_warp_match_fails': 'Hopper.Unified.checkNativeSync Kernels.HopperStage.block HopperCollectiveCycleTests.candidate (HopperCollectiveCycleTests.eid 1 2) (HopperCollectiveCycleTests.eid 0 0) = false',
    'native_cycle_fence_creates_tensor_reader': '(HopperCollectiveCycleTests.candidate.representativeAt (HopperCollectiveCycleTests.eid 0 0)).isSome = true',
    'stage_witness_native_reads_initial': 'Kernels.HopperStage.readWitness (Kernels.HopperStage.nativeRead UnifiedMemoryTests.firstA) ⟨.shared .zero,16⟩ = none',
    'stage_witness_input_reads_native_writer': '(Kernels.HopperStage.readWitness (.base (.tma (.read (Kernels.HopperStage.copyId 5) 0))) ⟨.global,65536⟩).isSome = true',
    'stage_witness_a_selects_b_writer': 'Kernels.HopperStage.readWitness (Kernels.HopperStage.nativeRead UnifiedMemoryTests.firstA) ⟨.shared .zero,16⟩ = some (.base (.tma (.write (Kernels.HopperStage.copyId 6) 0)))',
    'stage_native_rank_precedes_producer': 'Kernels.HopperStage.memoryRank (Kernels.HopperStage.nativeRead UnifiedMemoryTests.firstA) < Kernels.HopperStage.memoryRank (Kernels.HopperStage.nativeProducer UnifiedMemoryTests.firstA)',
    'stage_wait_rank_precedes_native': 'Kernels.HopperStage.memoryRank (.base (.tma (.source (Kernels.HopperStage.nativeWaitId 127)))) < Kernels.HopperStage.memoryRank (Kernels.HopperStage.nativeRead UnifiedMemoryTests.firstA)',
    'stage_mma_source_has_wait_rank': 'Kernels.HopperStage.sourceControlRank (Kernels.HopperStage.mmaId 0) = 330',
    'stage_wait_source_has_mma_rank': 'Kernels.HopperStage.sourceControlRank (Kernels.HopperStage.nativeWaitId 127) = 310',
    'stage_last_output_owner_is_first': 'Kernels.HopperStage.outputOwner 10239 = (0,0)',
    'stage_first_output_owner_is_last': 'Kernels.HopperStage.outputOwner 8192 = (127,3)',
    'stage_observer_omits_first_output': '¬ (⟨.global,8192⟩ : ISA.Location) ∈ Kernels.HopperStage.outputDomain',
    'stage_observer_covers_shared_alias': '(⟨.shared .zero,8192⟩ : ISA.Location) ∈ Kernels.HopperStage.outputDomain',
    'stage_observer_excludes_upper_guard': '¬ (⟨.global,10240⟩ : ISA.Location) ∈ Kernels.HopperStage.outputDomain',
    'native_first_a_uses_b_transfer': 'Kernels.HopperStage.nativeProducer UnifiedMemoryTests.firstA = .base (.tma (.write (Kernels.HopperStage.copyId 6) 0))',
    'native_first_a_uses_second_byte': 'Kernels.HopperStage.nativeProducer UnifiedMemoryTests.firstA = .base (.tma (.write (Kernels.HopperStage.copyId 5) 1))',
    'native_last_b_uses_a_transfer': 'Kernels.HopperStage.nativeProducer UnifiedMemoryTests.lastB = .base (.tma (.write (Kernels.HopperStage.copyId 5) 255))',
    'native_last_b_drops_last_byte': 'Kernels.HopperStage.nativeProducer UnifiedMemoryTests.lastB = .base (.tma (.write (Kernels.HopperStage.copyId 6) 254))',
    'native_reader_is_generic_proxy': '(Kernels.HopperStage.nativeRead UnifiedMemoryTests.firstA).proxy = .generic',
    'native_reader_footprint_is_float_word': '(Hopper.Unified.kind Hopper.Tma.localShared Hopper.Access.globalDescriptor (Kernels.HopperStage.candidate UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB) (Kernels.HopperStage.nativeRead UnifiedMemoryTests.firstA)).bind Event.Kind.footprint = some (⟨.shared .zero,16⟩,4)',
    'native_operand_read_writes_shared': '(Hopper.Unified.writeByte Hopper.Tma.localShared Hopper.Access.globalDescriptor (Kernels.HopperStage.candidate UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB) (Kernels.HopperStage.nativeRead UnifiedMemoryTests.firstA) ⟨.shared .zero,16⟩).isSome = true',
    'native_operand_read_covers_global_alias': '(Hopper.Unified.readByte Hopper.Tma.localShared Hopper.Access.globalDescriptor (Kernels.HopperStage.candidate UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB) (Kernels.HopperStage.nativeRead UnifiedMemoryTests.firstA) ⟨.global,16⟩).isSome = true',
    'native_last_b_ends_before_last_byte': 'Kernels.HopperStage.nativeLocation UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB UnifiedMemoryTests.lastB = ⟨.shared .zero,2318⟩',
    'native_first_a_overlaps_barrier_object': 'Kernels.HopperStage.nativeLocation UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB UnifiedMemoryTests.firstA = ⟨.shared .zero,0⟩',
    'native_prefix_leader_has_returned_count': '(Kernels.HopperStage.prefixTrace UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB 0).count = 47',
    'native_prefix_peer_has_returned_count': '(Kernels.HopperStage.prefixTrace UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB 127).count = 41',
    'native_prefix_empty_committed_groups': '(Kernels.HopperStage.prefixTrace UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB 127).final.ledger.groups = 0',
    'native_prefix_commit_completed_group': '(Kernels.HopperStage.prefixTrace UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB 127).final.ledger.completed = 1',
    'native_prefix_pending_erased': '(Hopper.Wgmma.pending (Kernels.HopperStage.prefixTrace UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB 127).final.ledger).length = 0',
    'native_prefix_is_done': '((Kernels.HopperStage.prefixTrace UnifiedMemoryTests.zerosA UnifiedMemoryTests.zerosB 127).final.base.scalar.core.thread.status == .done) = true',
    'native_leader_wait_aliases_peer_serial': '(Kernels.HopperStage.nativeWaitId 0).serial = 6',
    'native_peer_wait_aliases_leader_serial': '(Kernels.HopperStage.nativeWaitId 127).serial = 11',
    'native_wait_mark_skips_commit_sequence': '(Kernels.HopperStage.nativeWaitMark 0).sequence = 1',
    'native_output_word_last_overflows': 'Kernels.HopperStage.wordAddress 127 3+4 = 10244',
    'aligned_empty_commit_source_is_admitted': 'Hopper.Unified.SchedulesAdmitted Kernels.HopperStage.block UnifiedScheduleTests.candidate',
    'aligned_component_forces_uniform_local_d': 'Hopper.Unified.participantMatches Kernels.HopperStage.block (UnifiedScheduleTests.scaleTrace 0 true) (UnifiedScheduleTests.scaleTrace 1 false) 1 = false',
    'aligned_raw_signature_forgets_local_d': '(UnifiedScheduleTests.scaleTrace 0 true).nativeSchedule = (UnifiedScheduleTests.scaleTrace 1 false).nativeSchedule',
    'aligned_stage_drops_empty_groups_or_waits': 'Kernels.HopperStage.stageSchedule.length = 3',
    'aligned_stage_wait_uses_keep_one': '(Kernels.HopperStage.stageSchedule[3]?).map (fun sig => match sig.kind with | .wait _ keep => keep | _ => 99) = some 1',
    'hopper_initial_descriptor_offset_wrong': '(match HopperStageAdmissionTests.input ⟨.global,4096⟩ with | .tensorMapPart _ index => some index | _ => none) = some 1',
    'hopper_initial_a_descriptor_uses_b_base': '(match HopperStageAdmissionTests.input ⟨.global,4096⟩ with | .tensorMapPart view _ => some view.base | _ => none) = some 69632',
    'hopper_initial_a_last_byte_is_first_fragment': '(match HopperStageAdmissionTests.input ⟨.global,67583⟩ with | .realPart _ _ index => some index | _ => none) = some 0',
    'hopper_initial_b_uses_integer_byte': '(match HopperStageAdmissionTests.input ⟨.global,69887⟩ with | .bits _ => true | _ => false) = true',
    'hopper_initial_output_guard_zeroed': '(match HopperStageAdmissionTests.input ⟨.global,10240⟩ with | .bits value => some value | _ => none) = some (ISA.byte 0)',
    'hopper_stage_history_drops_one_resource': 'Kernels.HopperStage.resourceHistory.length = 132',
    'hopper_stage_missing_a_notice_returns': '(Hopper.Mbarrier.run none ((HopperStageAdmissionTests.droppedNotice 5).map Hopper.Tma.Entry.operation)).isSome = true',
    'hopper_stage_missing_b_notice_returns': '(Hopper.Mbarrier.run none ((HopperStageAdmissionTests.droppedNotice 6).map Hopper.Tma.Entry.operation)).isSome = true',
    'hopper_stage_early_invalidation_returns': '(Hopper.Mbarrier.run none (HopperStageAdmissionTests.earlyInvalidation.map Hopper.Tma.Entry.operation)).isSome = true',
    'hopper_stage_early_invalidation_detected_by_source_order_alone': '¬Hopper.Tma.SourceOrder HopperStageAdmissionTests.earlyInvalidation',
    'hopper_stage_last_peer_observes_wrong_transfer': 'Hopper.Tma.observation Kernels.HopperStage.resourceHistory 2 131 = some (Kernels.HopperStage.copyId 6,Kernels.HopperStage.waitId 127)',
    'hopper_stage_last_wait_is_uninitialized_lifetime': 'Hopper.Tma.lifetimeBefore Kernels.HopperStage.resourceHistory 131 = 0',
    'hopper_stage_last_wait_uses_precompletion_phase': 'Hopper.Tma.stampBefore Kernels.HopperStage.resourceHistory 131 = some ⟨1,0⟩',
    'hopper_stage_peer_cta_arrival_has_initial_rank': 'Kernels.HopperStage.sourceControlRank ⟨(Kernels.HopperStage.ctx 1).id,0⟩ = 0',
    'hopper_stage_a_notice_understates_byte_count': '(Hopper.Tma.resourceAt Hopper.Tma.localShared Kernels.HopperStage.resourceCandidate (.notification (Kernels.HopperStage.copyId 5))).map (fun event => match event.operation with | .completeTx count => count | _ => 0) = some 2047',
    'unified_projection_drops_native_slots': 'UnifiedTests.good.view.traces[0]?.map (fun trace => trace.events.length) = some 1',
    'unified_projection_turns_mma_into_memory': '(Hopper.Unified.kind Hopper.Tma.localShared Hopper.Access.globalDescriptor UnifiedTests.good (.base (.tma (.source (UnifiedTests.eid 1))))).isSome = true',
    'unified_projection_turns_mma_into_barrier': '(UnifiedTests.good.view.barrierAt (UnifiedTests.eid 1)).isSome = true',
    'unified_projection_turns_mma_into_cta_arrival': '(UnifiedTests.good.view.ctaTag true (UnifiedTests.eid 1)).isSome = true',
    'unified_store_renumbered_after_projection': '(UnifiedTests.good.view.eventAt (UnifiedTests.eid 0)).map (fun event => match event with | .ampere (.ordinary (.write _ _)) => true | _ => false) = some true',
    'unified_fence_invents_mma_representative': '(UnifiedTests.good.representativeAt (UnifiedTests.eid 0)).isSome = true',
    'unified_fake_tag_invents_mma_representative': '(UnifiedTests.fake.representativeAt (UnifiedTests.eid 0)).isSome = true',
    'unified_fake_tag_invents_operand_read': '(Hopper.Unified.kind Hopper.Tma.localShared Hopper.Access.globalDescriptor UnifiedTests.fake (.wgmmaRead (UnifiedTests.eid 0) (.a (0,0) 0))).isSome = true',
    'unified_return_implies_empty_pending': '(Hopper.Wgmma.pending UnifiedTests.badResult.1.ledger).length = 0',
    'unified_old_interpreter_accepts_native_source': '(Hopper.run UnifiedTests.ctx UnifiedTests.oracle.base UnifiedTests.goodCode 9 {}).toOption.isSome = true',
    'unified_wgmma_read_uses_generic_proxy': '(Hopper.Unified.Node.wgmmaRead (UnifiedTests.eid 1) (.a (0,0) 0)).proxy = .generic',
    'unified_wgmma_reuses_tma_memory_agent': '(Hopper.Unified.Node.wgmmaRead (UnifiedTests.eid 1) (.a (0,0) 0)).memoryAgent = (Hopper.Unified.Node.base (.tma (.read ⟨UnifiedTests.eid 1⟩ 0))).memoryAgent',
    'hopper_stage_leader_omits_transfer_steps': 'Kernels.HopperStage.count 0 = 41',
    'hopper_stage_peer_executes_leader_steps': 'Kernels.HopperStage.count 127 = 47',
    'hopper_stage_leader_mma_renumbered': '(Kernels.HopperStage.mmaId 0).serial = 4',
    'hopper_stage_peer_mma_renumbered': '(Kernels.HopperStage.mmaId 127).serial = 9',
    'hopper_stage_leader_mma_reuses_peer_query': '(Kernels.HopperStage.calls WgmmaTensorTests.onesA WgmmaTensorTests.onesB 0).query = 1',
    'hopper_stage_peer_mma_reuses_leader_query': '(Kernels.HopperStage.calls WgmmaTensorTests.onesA WgmmaTensorTests.onesB 127).query = 5',
    'hopper_stage_b_overlaps_a_base': '(Hopper.Wgmma.MatrixDescriptor.decode 68720001153).base = 2048',
    'hopper_stage_last_store_at_first_word': 'Kernels.HopperStage.outFinal 127+Kernels.HopperStage.storeOffset 3 = 8192',
    'hopper_stage_last_store_drops_high_rows': '(Kernels.HopperStage.storeId 127 3).serial = 7',
    'wgmma_descriptor_allows_reserved_start_bits': 'Hopper.Wgmma.MatrixDescriptor.Canonical (Hopper.Wgmma.packedA+2^14)',
    'wgmma_descriptor_allows_reserved_leading_bits': 'Hopper.Wgmma.MatrixDescriptor.Canonical (Hopper.Wgmma.packedA+2^30)',
    'wgmma_descriptor_allows_reserved_stride_bits': 'Hopper.Wgmma.MatrixDescriptor.Canonical (Hopper.Wgmma.packedA+2^46)',
    'wgmma_packed_profile_accepts_nonzero_base_offset': 'Hopper.Wgmma.MatrixDescriptor.Packed (Hopper.Wgmma.packedA+2^49)',
    'wgmma_packed_profile_accepts_swizzle': 'Hopper.Wgmma.MatrixDescriptor.Packed (Hopper.Wgmma.packedA+2^62)',
    'wgmma_descriptor_silently_truncates_high_bits': 'Hopper.Wgmma.MatrixDescriptor.Canonical (Hopper.Wgmma.packedA+2^64)',
    'wgmma_old_overlapping_a_is_packed': 'Hopper.Wgmma.MatrixDescriptor.Packed 34359803904',
    'wgmma_old_overlapping_b_is_packed': 'Hopper.Wgmma.MatrixDescriptor.Packed 34359804032',
    'wgmma_accumulator_ignores_warp_index': 'Hopper.Wgmma.cCoord (32,0) = (0,0)',
    'wgmma_accumulator_lower_rows_alias_upper': 'Hopper.Wgmma.cCoord (0,2) = (0,0)',
    'wgmma_accumulator_last_row_belongs_to_first_warp': '(Hopper.Wgmma.cOwner (63,7)).1 = 31',
    'wgmma_shared_a_is_plain_row_major': 'Hopper.Wgmma.aAddress (Hopper.Wgmma.MatrixDescriptor.decode Hopper.Wgmma.packedA) (1,0) 0 = 32',
    'wgmma_shared_b_is_plain_column_major': 'Hopper.Wgmma.bAddress (Hopper.Wgmma.MatrixDescriptor.decode Hopper.Wgmma.packedB) (0,1) 0 = 2080',
    'wgmma_a_crosses_b_arena': 'Hopper.Wgmma.aAddress (Hopper.Wgmma.MatrixDescriptor.decode Hopper.Wgmma.packedA) (63,15) 1 = 2048',
    'wgmma_operand_inventory_omits_last_byte': '(Hopper.Wgmma.OperandByte.b (15,7) 1).index = 2302',
    'wgmma_operand_uses_generic_proxy': 'Hopper.Wgmma.readProxy = Hopper.Tma.Proxy.generic',
    'wgmma_generic_read_needs_no_refence': '(Hopper.Wgmma.run WgmmaProtocolTests.ctx WgmmaProtocolTests.oracle [WgmmaProtocolTests.fence,WgmmaProtocolTests.mma,WgmmaProtocolTests.commit,WgmmaProtocolTests.wait0,WgmmaProtocolTests.store,WgmmaProtocolTests.mma] 6 WgmmaProtocolTests.seed).toOption.isSome = true',
    'wgmma_wait_eight_is_accepted': '(Hopper.Wgmma.run WgmmaProtocolTests.ctx WgmmaProtocolTests.oracle [.wgmma (.wait 8)] 1 WgmmaProtocolTests.seed).toOption.isSome = true',
    'wgmma_integer_scale_register_is_typed': 'Hopper.Wgmma.InstructionTyped Generated.wgmma_probe.registerDeclarations (.mma WgmmaProtocolTests.d "%a" "%b" (.reg "%thread"))',
    'wgmma_issue_without_fence': '(Hopper.Wgmma.run WgmmaProtocolTests.ctx WgmmaProtocolTests.oracle [WgmmaProtocolTests.mma] 1 WgmmaProtocolTests.seed).toOption.isSome = true',
    'wgmma_generic_read_before_wait': '(Hopper.Wgmma.run WgmmaProtocolTests.ctx WgmmaProtocolTests.oracle [WgmmaProtocolTests.fence,WgmmaProtocolTests.mma,WgmmaProtocolTests.store] 3 WgmmaProtocolTests.seed).toOption.isSome = true',
    'wgmma_generic_write_before_wait': '(Hopper.Wgmma.run WgmmaProtocolTests.ctx WgmmaProtocolTests.oracle [WgmmaProtocolTests.fence,WgmmaProtocolTests.mma,WgmmaProtocolTests.overwrite] 3 WgmmaProtocolTests.seed).toOption.isSome = true',
    'wgmma_commit_is_completion': '(Hopper.Wgmma.run WgmmaProtocolTests.ctx WgmmaProtocolTests.oracle [WgmmaProtocolTests.fence,WgmmaProtocolTests.mma,WgmmaProtocolTests.commit,WgmmaProtocolTests.store] 4 WgmmaProtocolTests.seed).toOption.isSome = true',
    'wgmma_wait_implicitly_commits': '(Hopper.Wgmma.run WgmmaProtocolTests.ctx WgmmaProtocolTests.oracle [WgmmaProtocolTests.fence,WgmmaProtocolTests.mma,WgmmaProtocolTests.wait0,WgmmaProtocolTests.store] 4 WgmmaProtocolTests.seed).toOption.isSome = true',
    'wgmma_wait_one_must_drain_latest_group': '(Hopper.Wgmma.run WgmmaProtocolTests.ctx WgmmaProtocolTests.oracle [WgmmaProtocolTests.fence,WgmmaProtocolTests.mma,WgmmaProtocolTests.commit,.wgmma (.wait 1),WgmmaProtocolTests.store] 5 WgmmaProtocolTests.seed).toOption.isSome = true',
    'wgmma_dirty_register_needs_no_fence': '(Hopper.Wgmma.run WgmmaProtocolTests.ctx WgmmaProtocolTests.oracle [WgmmaProtocolTests.fence,WgmmaProtocolTests.overwrite,WgmmaProtocolTests.mma] 3 WgmmaProtocolTests.seed).toOption.isSome = true',
    'wgmma_fence_is_completion': '(Hopper.Wgmma.run WgmmaProtocolTests.ctx WgmmaProtocolTests.oracle [WgmmaProtocolTests.fence,WgmmaProtocolTests.mma,WgmmaProtocolTests.fence,WgmmaProtocolTests.store] 4 WgmmaProtocolTests.seed).toOption.isSome = true',
    'wgmma_legacy_entry_silently_skips_instruction': '(Hopper.step WgmmaProtocolTests.ctx WgmmaProtocolTests.oracle.base [WgmmaProtocolTests.fence] {}).toOption.isSome = true',
    'wgmma_empty_commit_erases_group_identity': '(WgmmaProtocolTests.result [WgmmaProtocolTests.fence,WgmmaProtocolTests.commit,WgmmaProtocolTests.commit,WgmmaProtocolTests.wait0] 4).1.ledger.groups = 0',
    'wgmma_issue_has_no_pending_accumulators': '(Hopper.Wgmma.pending (WgmmaProtocolTests.result [WgmmaProtocolTests.fence,WgmmaProtocolTests.mma] 2).1.ledger).length = 0',
    'wgmma_source_drops_store_pc': '(WgmmaSourceTests.result 0).2.map SourceRun.Located.pc = [10,11,12,13]',
    'wgmma_source_aliases_all_lanes_to_zero': '((WgmmaSourceTests.result 127).1.ledger.calls[0]?).map (fun call => call.lane.val) = some 0',
    'wgmma_wait_reuses_issue_query': '(WgmmaSourceTests.result 0).1.base.scalar.core.queries = 1',
    'tma_observer_can_select_initial_output': 'TmaConsumerObserver.observation.source ⟨.global,8192⟩ = none',
    'tma_observer_can_select_consumer_instead_of_store': 'TmaConsumerObserver.observation.source ⟨.global,8192⟩ = some (.tma (.source (TmaPublicationTests.eid 5)))',
    'tma_observer_treats_padding_as_written': '(TmaConsumerObserver.select ⟨.global,8196⟩).isSome = true',
    'tma_observer_domain_has_no_guard_bytes': 'TmaConsumerObserver.domain.length = 4',
    'tma_observer_drops_last_output_byte': '(⟨.global,8195⟩ : ISA.Location) ∉ TmaConsumerObserver.domain',
    'tma_observer_drops_guard_byte': '(⟨.global,8196⟩ : ISA.Location) ∉ TmaConsumerObserver.domain',
    'tma_global_observer_contains_shared_memory': '(⟨.shared .zero,16⟩ : ISA.Location) ∈ TmaConsumerObserver.domain',
    'tma_observer_writes_padding_from_output_event': 'TmaConsumerObserver.observation.source ⟨.global,8196⟩ = some (.tma (.source (TmaPublicationTests.eid 6)))',
    'tma_race_reader_footprint_is_one_byte': '(Hopper.Access.kind Hopper.Tma.localShared Hopper.Access.globalDescriptor TmaRaceTests.candidate TmaRaceTests.read).bind Event.Kind.footprint = some (TmaRaceTests.loc,1)',
    'tma_race_writer_footprint_is_four_bytes': '(Hopper.Access.kind Hopper.Tma.localShared Hopper.Access.globalDescriptor TmaRaceTests.candidate TmaRaceTests.writer).bind Event.Kind.footprint = some (TmaRaceTests.loc,4)',
    'tma_race_has_distinct_physical_owners': 'TmaRaceTests.read.owner ≠ TmaRaceTests.writer.owner',
    'tma_shared_issuer_implies_same_proxy': 'TmaRaceTests.read.proxy = TmaRaceTests.writer.proxy',
    'tma_shared_issuer_implies_same_memory_agent': 'TmaRaceTests.read.memoryAgent = TmaRaceTests.writer.memoryAgent',
    'tma_initial_source_rank_is_one': 'Hopper.Access.sourceRank (fun _ => 7) none = 1',
    'tma_written_source_rank_is_not_shifted': 'Hopper.Access.sourceRank (fun _ => 7) (some TmaRaceTests.writer) = 7',
    'tma_observation_reuses_old_phase_after_parity_wrap': '(Hopper.Tma.observation TmaPhaseTests.three 2 9).isSome = true',
    'tma_observation_survives_object_reinitialization': '(Hopper.Tma.observation TmaPhaseTests.restarted 2 8).isSome = true',
    'tma_observation_drops_new_object_notification': '(Hopper.Tma.observation TmaPhaseTests.restarted 7 8).isSome = false',
    'tma_explicit_complete_tx_publishes_transfer': '(Hopper.Tma.observation TmaPhaseTests.explicitOnly 2 3).isSome = true',
    'tma_false_wait_publishes_bytes': '(Hopper.Tma.observation TmaPhaseTests.falseWait 2 3).isSome = true',
    'tma_completion_can_be_observed_backwards': '(Hopper.Tma.observation TmaPhaseTests.first 2 1).isSome = true',
    'tma_notice_uses_postcompletion_phase': 'Hopper.Tma.stampBefore TmaPublicationTests.history 2 = some ⟨1,1⟩',
    'tma_wait_keeps_precompletion_phase': 'Hopper.Tma.stampBefore TmaPublicationTests.history 3 = some ⟨1,0⟩',
    'tma_reinitialized_lifetime_is_unchanged': 'Hopper.Tma.lifetimeBefore TmaPhaseTests.restarted 8 = 1',
    'tma_consumer_branch_target_erased': 'Hopper.sourcePC (TmaPublicationTests.candidate 0) Generated.hopper_tma_publish.program TmaPublicationTests.params .one (TmaPublicationTests.eid 5) = some 11',
    'tma_consumer_assembled_word_is_zero': 'Ptx.wrap 32 TmaPublicationTests.answer = 0',
    'tma_missing_fence_keeps_three_events': 'TmaPhaseTests.noFenceTrace.events.length = 3',
    'tma_combined_drops_ordinary_store': '(Hopper.Access.writeByte Hopper.Tma.localShared Hopper.Access.globalDescriptor TmaInputTests.ordinaryOverwrite (.tma (.source (TmaTests.eid 0))) ⟨.global,196⟩).isSome = false',
    'tma_combined_drops_nonbulk_store': '(Hopper.Access.writeByte Hopper.Tma.localShared Hopper.Access.globalDescriptor TmaInputTests.nonbulkOverwrite (.copyWrite (TmaTests.eid 0)) ⟨.shared .zero,196⟩).isSome = false',
    'tma_combined_drops_rmw_read': '(Hopper.Access.readByte Hopper.Tma.localShared Hopper.Access.globalDescriptor TmaInputTests.rmwOverwrite (.tma (.source (TmaTests.eid 0))) ⟨.global,196⟩).isSome = false',
    'tma_combined_drops_rmw_write': '(Hopper.Access.writeByte Hopper.Tma.localShared Hopper.Access.globalDescriptor TmaInputTests.rmwOverwrite (.tma (.source (TmaTests.eid 0))) ⟨.global,196⟩).isSome = false',
    'tma_opaque_object_truncated': '(ISA.TensorMap.encode TmaTests.view).length = 64',
    'tma_descriptor_pointer_is_generic_proxy': '(Hopper.Access.Node.tma (.descriptor TmaTests.operation)).proxy = .generic',
    'tma_oob_invents_input_read': '(Hopper.Tma.readLocation TmaInputTests.zeroCandidate TmaInputTests.zeroOperation 0).isSome = true',
    'tma_oob_drops_destination_write': '(Hopper.Tma.writeLocation Hopper.Tma.localShared TmaInputTests.zeroCandidate TmaInputTests.zeroOperation 0).isSome = false',
    "tma_copy_ignores_row_stride": "Hopper.Tma.readLocation TmaTests.candidate TmaTests.operation 16 = some ⟨.global,212⟩",
    "tma_descriptor_uses_async_data_proxy": "(Hopper.Tma.Node.descriptor TmaTests.operation).proxy = (Hopper.Tma.Node.read TmaTests.operation 0).proxy",
    "tma_completion_is_issuer_agent": "(Hopper.Tma.Node.notify TmaTests.operation).agent = (Hopper.Tma.Node.source TmaTests.operation.issue).agent",
    "tma_signed_coordinate_kept_unsigned": "Hopper.Tma.signed32 4294967295 = (4294967295 : Int)",
    "tma_notification_wrong_byte_count": "Hopper.Tma.notification Hopper.Tma.localShared TmaTests.candidate TmaTests.operation = some ⟨TmaTests.loc,.completeTx 16⟩",
    "tma_duplicate_completion_has_unique_identity": "(TmaTests.duplicateNotify.map Hopper.Tma.Entry.origin).Nodup",
    "tma_short_payload_source_returns": "(Hopper.run TmaTests.ctx TmaTests.shortOracle Generated.hopper_tma_copy.program 13 {}).toOption.isSome = true",
    "tma_wait_can_drop_implicit_notification": "(Hopper.Mbarrier.run none [.init 1,.arriveExpectTx 32,.tryWaitParity 0 true,.inval]).isSome = true",
    "hopper_resource_missing_peer_wait": "HopperResourceTests.droppedPeer.Perm (HopperResourceTests.candidate.barrierInventory (HopperResourceTests.loc 0))",
    "hopper_resource_duplicate_identity": "(HopperResourceTests.duplicateEntry.map Hopper.ResourceEntry.id).Nodup",
    "hopper_resource_wrong_thread_order": "Hopper.ThreadOrder HopperResourceTests.reversedLeader",
    "hopper_resource_ghost_notification_matches_source": "HopperResourceTests.ghostComplete.Perm (HopperResourceTests.badCandidate.barrierInventory HopperMbarrierTests.loc)",
    "hopper_resource_cross_cta_notification": "Hopper.ResourceEdge HopperResourceTests.candidate HopperResourceTests.histories (HopperResourceTests.eid 0 0 4) (HopperResourceTests.eid 1 1 2)",
    "hopper_resource_invalidation_before_peer_wait": "HopperResourceTests.rank (HopperResourceTests.eid 0 0 8) < HopperResourceTests.rank (HopperResourceTests.eid 0 1 2)",
    "hopper_resource_cycle_reorders_wait_before_signal": "(Hopper.Mbarrier.run none [.init 1,.tryWaitParity 0 true,.arriveExpectTx 0]).isSome = true",
    "hopper_wait_before_tx_completion": "(Hopper.Mbarrier.run none HopperMbarrierTests.badOps).isSome = true",
    "hopper_reuse_without_successful_wait": "(Hopper.Mbarrier.run none [.init 1,.arriveExpectTx 0,.arriveExpectTx 0]).isSome = true",
    "hopper_false_wait_publishes_reuse": "(Hopper.Mbarrier.run none [.init 1,.arriveExpectTx 0,.tryWaitParity 0 false,.arriveExpectTx 0]).isSome = true",
    "hopper_completion_ignores_missing_arrival": "(Hopper.Mbarrier.run none [.init 2,.arriveExpectTx 16,.completeTx 16,.tryWaitParity 0 true]).isSome = true",
    "hopper_stale_phase_parity_reused": "(Hopper.Mbarrier.run none [.init 1,.arriveExpectTx 0,.tryWaitParity 0 true,.arriveExpectTx 0,.tryWaitParity 0 true]).isSome = true",
    "hopper_signed_tx_saturated_to_zero": "Hopper.Mbarrier.run none [.init 1,.completeTx 16] = some (some ⟨0,1,1,0,true⟩)",
    "hopper_double_initialization_allowed": "(Hopper.Mbarrier.run none [.init 1,.init 1]).isSome = true",
    "hopper_overflowed_arrival_count_allowed": "(Hopper.Mbarrier.run none [.init (2^20)]).isSome = true",
    "tiled_memory_shared_read_initial_source": "AmpereTiledWitnessMemory.rf (.thread ⟨AmpereTiledPhaseTests.reader,24⟩) ⟨.shared AmpereTiledPhaseTests.reader.cta,236⟩ = none",
    "tiled_memory_shared_read_future_source": "AmpereTiledWitnessMemory.rf (.thread ⟨AmpereTiledPhaseTests.reader,24⟩) ⟨.shared AmpereTiledPhaseTests.reader.cta,236⟩ = some (.copyWrite ⟨AmpereTiledPhaseTests.writer,6⟩)",
    "tiled_memory_input_read_uses_copy_writer": "AmpereTiledWitnessMemory.rf (.copyRead ⟨AmpereTiledPhaseTests.writer,3⟩) ⟨.global,2380⟩ = some (.copyWrite ⟨AmpereTiledPhaseTests.writer,0⟩)",
    "tiled_memory_future_copy_before_read": "AmpereTiledControl.rank (.copyWrite ⟨AmpereTiledPhaseTests.writer,6⟩) ≤ AmpereTiledControl.rank (.thread ⟨AmpereTiledPhaseTests.reader,24⟩)",
    "tiled_witness_copy_completes_after_wait": "AmpereTiledControl.rank (.copyWrite ⟨AmpereTiledPhaseTests.reader,8⟩) ≥ AmpereTiledControl.rank (.thread ⟨AmpereTiledPhaseTests.reader,38⟩)",
    "tiled_witness_lane_zero_as_last_lane": "AmpereTiledWitnessMma.peer AmpereTiledPhaseTests.reader 0 = AmpereTiledPhaseTests.reader",
    "tiled_witness_mma_entry_as_return": "(AmpereTiledWitnessMma.members AmpereTiledPhaseTests.input AmpereTiledCorrectTests.representedLaunch AmpereTiledCorrectTests.left AmpereTiledCorrectTests.right AmpereTiledPhaseTests.reader 2 31).entry.serial = 48",
    "tiled_witness_mma_as_post_barrier_pc": "(AmpereTiledWitnessMma.call AmpereTiledPhaseTests.input AmpereTiledCorrectTests.representedLaunch AmpereTiledCorrectTests.left AmpereTiledCorrectTests.right AmpereTiledPhaseTests.reader 2).pc = 72",
    "tiled_upper_a_fragment_as_lower_row": "(AmpereTiledProducer.inputBase AmpereTiledPhaseTests.input AmpereTiledPhaseTests.reader 2 3).address = 2428",
    "tiled_b_fragment_wrong_k_stride": "(AmpereTiledProducer.inputBase AmpereTiledPhaseTests.input AmpereTiledPhaseTests.reader 2 5).address = 9692",
    "tiled_first_read_uses_reader_copy": "AmpereTiledProducer.producer AmpereTiledPhaseTests.reader 0 = AmpereTiledPhaseTests.reader",
    "tiled_a_fragment_uses_b_copy": "AmpereTiledProducer.part 3 = 2",
    "tiled_last_store_uses_low_rows": "AmpereTiledOutputLayout.row AmpereTiledPhaseTests.reader 3 = 23",
    "tiled_last_store_uses_first_column": "AmpereTiledOutputLayout.col AmpereTiledPhaseTests.reader 3 = 14",
    "tiled_output_padding_as_matrix": "(18432 : Nat) < AmpereTiledPhaseTests.input.c+4*(AmpereTiledPhaseTests.input.m*AmpereTiledPhaseTests.input.n)",
    "tiled_last_store_overruns_word": "(AmpereTiledInventory.writeBase AmpereTiledPhaseTests.input (AmpereTiledGraph.context AmpereTiledPhaseTests.launch AmpereTiledPhaseTests.reader) 3).address+4 = 18436",
    "tiled_copy_write_rejoins_thread_agent": "Ampere.Node.agent (.copyWrite ⟨AmpereTiledPhaseTests.writer,3⟩) = Ampere.Node.agent (.thread ⟨AmpereTiledPhaseTests.reader,24⟩)",
    "tiled_reused_phase_keeps_same_agent": "Ampere.Node.agent (.copyWrite ⟨AmpereTiledPhaseTests.writer,3⟩) = Ampere.Node.agent (.copyWrite ⟨AmpereTiledPhaseTests.writer,6⟩)",
    "tiled_second_half_copy_start_as_read": "AmpereTiledSharedWriters.copyBase AmpereTiledPhaseTests.writer 0 = 236",
    "tiled_four_cta_source_as_single_warp": "AmpereTiledPhaseTests.launch.geometry.grid.volume*AmpereTiledPhaseTests.launch.geometry.block.volume = 32",
    "tiled_late_short_copy_reply_accepted": "(AmpereTiledReconstructionTests.shortThirdCopy.bytes 22).length = 8",
    "tiled_late_b_integer_as_packed": "(AmpereTiledReconstructionTests.integerSecondB.word32 18).packedValue.isSome = true",
    "tiled_late_a_integer_as_packed": "(AmpereTiledReconstructionTests.integerThirdA.word32 24).packedValue.isSome = true",
    "tiled_stale_packed_survives_integer_load": '(ISA.declarationLookup "%rb1" (Ampere.RawLoads.loaded AmpereTiledReconstructionTests.old AmpereTiledReconstructionTests.badA AmpereTiledReconstructionTests.badB).packed).isSome = true',
    "tiled_unused_matrix_slot_word_forced_packed": "(AmpereTiledReconstructionTests.matrixSlotInteger.word32 9).packedValue.isSome = true",
    "tiled_initialized_pc_skips_last_mov": "(AmpereTiledEntry.ready AmpereTiledSourceTests.cfg (AmpereTiledSourceTests.ctx AmpereTiledSourceTests.cfg AmpereTiledSourceTests.id)).scalar.core.thread.pc = 56",
    "tiled_initialized_nonzero_query": "(AmpereTiledEntry.ready AmpereTiledSourceTests.cfg (AmpereTiledSourceTests.ctx AmpereTiledSourceTests.cfg AmpereTiledSourceTests.id)).scalar.core.queries = 1",
    "tiled_actual_b_pointer_as_a": "AmpereTiledAddresses.b AmpereTiledSourceTests.cfg (AmpereTiledSourceTests.ctx AmpereTiledSourceTests.cfg AmpereTiledSourceTests.id) = 2360",
    "tiled_high_a_stride_as_constant_bytes": "AmpereTiledAddresses.ah AmpereTiledSourceTests.cfg (AmpereTiledSourceTests.ctx AmpereTiledSourceTests.cfg AmpereTiledSourceTests.id) = 2376",
    "tiled_zero_k_unused_reply_requirement": "(AmpereTiledSourceTests.hostileOracle.bytes 0).length = 8",
    "tiled_zero_k_unused_alias_as_aligned": "AmpereTiledSourceTests.zeroK.a%8 = 0",
    "tiled_far_cta_index_wraps": "AmpereTiledInit.tileCol (AmpereTiledSourceTests.ctx AmpereTiledSourceTests.rowMasked AmpereTiledSourceTests.farId) = 0",
    "tiled_last_a_copy_overruns": "AmpereTiledBounds.copyStart AmpereTiledSourceTests.cfg (AmpereTiledSourceTests.ctx AmpereTiledSourceTests.cfg AmpereTiledSourceTests.id) 2 1+8 = AmpereTiledSourceTests.cfg.a+2*(AmpereTiledSourceTests.cfg.m*AmpereTiledSourceTests.cfg.k)+1",
    "tiled_b_mistaken_for_row_major": "(AmpereTiledSpec.bLocation AmpereTiledSpecTests.nonzero 3 5).address = 2106",
    "tiled_nonzero_history_query_reset": "AmpereTiledStageTests.last.scalar.core.queries = 10",
    "tiled_nonzero_history_group_reset": "AmpereTiledStageTests.last.groups = 1",
    "tiled_nonzero_history_mma_reset": "AmpereTiledStageTests.last.mmaCalls = 1",
    "tiled_nonzero_history_generation_reset": "Ptx.Event.generation AmpereTiledStageTests.last.scalar.core 0 = 2",
    "tiled_nonzero_history_copy_reset": "AmpereTiledStageTests.last.copies.length = 3",
    "tiled_second_mma_reuses_first_ordinal": "AmpereTiledStageTests.captured.ordinal = 0",
    "tiled_second_mma_uses_first_pc": "AmpereTiledStageTests.captured.pc = 65",
    "tiled_copy_reply_as_packed_word_width": "(AmpereTiledLoopTests.oracle.bytes 14).length = (Ampere.Word32.encode (AmpereTiledLoopTests.oracle.word32 14)).length",
    "tiled_a_second_word_mistaken_for_copy_start": "Ampere.Tiled.aRead 3 7 3 = 504",
    "tiled_b_second_word_mistaken_for_copy_start": "Ampere.Tiled.bRead 3 7 1 = 760",
    "reused_buffer_observer_selects_old_write": "MemoryGraphRankedTests.observer.output MemoryGraphRankedTests.loc = 7",
    "reused_buffer_same_copy_agent": "MemoryGraphRankedTests.graph.agent 0 = MemoryGraphRankedTests.graph.agent 2",
    "tiled_barriers_have_unique_static_site": "Ampere.uniqueBarrierSites AmpereTiledTests.code = true",
    "tiled_loop_erased": "Generated.ampere_tiled_matmul.program.length = 82",
    "mma_wrong_source_length": "Generated.mma_probe.program.length = 24",
    "mma_wrong_query_count": "MmaLocalTests.trace.final.scalar.core.queries = 10",
    "mma_wrong_source_pc": "MmaLocalTests.call.pc = 20",
    "mma_oracle_controls_lane": "MmaLocalTests.call.lane = 1",
    "mma_wrong_call_count": "MmaLocalTests.trace.final.mmaCalls = 0",
    "packed_word_wrong_width": "(Ampere.Word32.encode (.integer 42)).length = 8",
    "copy_event_no_truncation": (
        "CopyEventTests.observedWord CopyInstances.maskedConfig (fun _ => ISA.byte 165) 5 = 4294967303"
    ),
    "copy_event_zeroed_unknown_frame": (
        "CopyEventTests.observedWord CopyEventTests.frameConfig (fun _ => ISA.byte 165) 0 = 0"
    ),
    "self_loop_as_forward_progress": "Termination.ForwardAt 0 (Instr.jump 0)",
    "self_loop_progress_as_completion": (
        "((run TerminationTests.loopCode [.thread 0] TerminationTests.loopMachine).toOption.map "
        "(fun m => m.threads.all (fun t => t.status == .done))) = some true"
    ),
    "shared_swap_as_plain_copy": (
        "SharedEventTests.observedWord SharedInstances.pair (fun _ => ISA.byte 165) 2 = 4294967295"
    ),
    "shared_swap_zeroed_unknown_frame": (
        "SharedEventTests.observedWord SharedEventTests.frameConfig (fun _ => ISA.byte 165) 0 = 0"
    ),
    "collective_release_as_thread_work": (
        "Termination.potential (Termination.threadWork 17) SharedRefinementTests.resumed.threads < "
        "Termination.potential (Termination.threadWork 17) SharedRefinementTests.arrived.threads"
    ),
    "typing_predicate_as_u32": (
        "ISA.InstructionTyped TypingTests.registers TypingTests.parameters 2 (Instr.mov 32 \"%p\" (.imm 0))"
    ),
    "typing_u32_pointer": (
        "ISA.InstructionTyped TypingTests.registers TypingTests.parameters 2 "
        "(Instr.load .global \"%r\" {base := .reg \"%r\"})"
    ),
    "typing_multiply_wide_narrow_destination": (
        "ISA.InstructionTyped TypingTests.registers TypingTests.parameters 2 "
        "(Instr.bin .mul 32 64 \"%r\" (.reg \"%b\") (.imm 4))"
    ),
    "typing_corrupt_declaration_environment": (
        "ISA.ProgramTyped [(\"%r\", ISA.RegisterType.u32),(\"%r\", ISA.RegisterType.u64)] [] [Instr.ret]"
    ),
    "scalar_f32_as_integer": (
        "Scalar.InstructionTyped [(\"%f\", Scalar.RegisterType.floating .f32)] [] 1 "
        "(Scalar.Instr.integer (.mov 32 \"%f\" (.imm 0)))"
    ),
    "scalar_u32_as_float": (
        "Scalar.InstructionTyped [(\"%x\", Scalar.RegisterType.integer .u32)] [] 1 "
        "(Scalar.Instr.mov .f32 \"%x\" (.reg \"%x\"))"
    ),
    "float_frontend_infinity_literal": "(2139095040 / 2^23) % 256 < (255 : Nat)",
    "float_frontend_nan_literal": "(2143289345 / 2^23) % 256 < (255 : Nat)",
    "special_float_destination": (
        "Scalar.InstructionTyped [(\"%f\", Scalar.RegisterType.floating .f32)] [] 1 "
        "(Scalar.Instr.readSpecial \"%f\" (.ntid .x))"
    ),
    "matmul_column_product_overflow": (
        "Scalar.col ScalarMatmulInitTests.overflow.block ScalarMatmulInitTests.overflow.id < 2^32"
    ),
    "atomic_float_destination": (
        "Scalar.InstructionTyped [(\"%f\", Scalar.RegisterType.floating .f32)] [] 1 "
        "(Scalar.Instr.atomAddU32 \"%f\" {base := .imm 64} (.imm 1))"
    ),
    "atomic_narrow_pointer": (
        "Scalar.InstructionTyped [(\"%r\", Scalar.RegisterType.integer .u32)] [] 1 "
        "(Scalar.Instr.atomAddU32 \"%r\" {base := .reg \"%r\"} (.imm 1))"
    ),
    "atomic_ticket_one_as_ten_steps": "AtomicDispatchTrace.sourceCount 1 = 10",
    "atomic_start_only_as_full_word_bound": "((2^64-1)+4 : Nat) ≤ 2^64",
    "ex2_integer_operand": (
        "Scalar.InstructionTyped [(\"%f\", Scalar.RegisterType.floating .f32), "
        "(\"%r\", Scalar.RegisterType.integer .u32)] [] 1 "
        "(Scalar.Instr.ex2Approx \"%f\" (.reg \"%r\"))"
    ),
    "max_integer_destination": (
        "Scalar.InstructionTyped [(\"%f\", Scalar.RegisterType.floating .f32), "
        "(\"%r\", Scalar.RegisterType.integer .u32)] [] 1 "
        "(Scalar.Instr.max .f32 \"%r\" (.reg \"%f\") (.reg \"%f\"))"
    ),
    "attention_first_key_as_update_count": (
        "ScalarAttentionOuter.suffixSteps ScalarAttentionOuterTests.layout.dim 0 "
        "ScalarAttentionOuterTests.layout.keys = 75"
    ),
    "attention_query_without_value_load": (
        "ScalarAttentionOuter.queryIndex ScalarAttentionOuterTests.layout 1 = 3"
    ),
    "attention_nonunit_output_without_row_stride": (
        "ScalarAttentionInit.outputAddress ScalarAttentionEntryTests.input "
        "(ScalarAttentionEntryTests.context ScalarAttentionEntryTests.input) = 4116"
    ),
    "attention_nonunit_column_as_local_tid": (
        "Scalar.col (ScalarAttentionEntryTests.context ScalarAttentionEntryTests.input).block "
        "(ScalarAttentionEntryTests.context ScalarAttentionEntryTests.input).id = 1"
    ),
    "divergent_barrier_as_single_aligned_site": (
        "ISA.barrierSites Generated.divergent_barrier.program 0 = [5]"
    ),
    "attention_read_start_as_word_bound": "(2^64-3 : Nat)+4 ≤ 2^64",
    "attention_live_scale_output_overlap": "Scalar.WordsDisjoint 256 1 256 9",
    "attention_empty_keys_read_inputs": "ScalarAttentionEvent.ReadsEnabled ScalarAttentionMemoryTests.zeroCfg.input",
    "divergent_barrier_forged_common_source": (
        "SourceOriginsTests.bad.sourcePC SourceOriginsTests.badCode SourceOriginsTests.badParams BarrierPublish.rr = some 9"
    ),
    "repeated_barrier_single_static_site": "ISA.uniqueBarrierSites SourceOriginsTests.repeatedCode = true",
    "repeated_barrier_second_source_as_first": (
        "SourceOriginsTests.repeated.sourcePC SourceOriginsTests.repeatedCode [] ⟨BarrierPublish.reader,3⟩ = some 0"
    ),
    "scalar_actual_block_source_as_unit": (
        "Scalar.sourcePC ScalarSourceOriginsTests.execution ScalarSourceOriginsTests.code [] ScalarSourceOriginsTests.block ⟨BarrierPublish.writer,0⟩ = none"
    ),
    "scalar_second_phase_source_as_first": (
        "Scalar.sourcePC ScalarSourceOriginsTests.execution ScalarSourceOriginsTests.code [] ScalarSourceOriginsTests.block ⟨BarrierPublish.writer,3⟩ = some 7"
    ),
    "scalar_divergent_barrier_forged_source": (
        "Scalar.sourcePC ScalarSourceOriginsTests.bad ScalarSourceOriginsTests.badCode SourceOriginsTests.badParams ScalarSourceOriginsTests.block BarrierPublish.rr = some 9"
    ),
    "stream_unobserved_payload_published": (
        "(match Event.published StreamTests.old StreamTests.poison ⟨.global,250⟩ with "
        "| .bits value => some value | _ => none) = some (ISA.byte 0)"
    ),
    "stream_shared_state_carried_between_launches": (
        "(match (StreamPipeline.matmul.launch StreamTests.heap).initial ⟨.shared ISA.Dim3.zero,0⟩ with "
        "| .bits value => some value | _ => none) = some (ISA.byte 17)"
    ),
    "stream_output_last_byte_unobserved": (
        "(⟨.global,67⟩ : ISA.Location) ∉ StreamPipeline.literal.domain"
    ),
    "float_compare_nonpredicate_destination": (
        'Scalar.InstructionTyped [("%r", Scalar.RegisterType.integer .u32), '
        '("%f", Scalar.RegisterType.floating .f32)] [] 1 '
        '(Scalar.Instr.setpGt .f32 "%r" (.reg "%f") (.reg "%f"))'
    ),
    "float_compare_integer_left_operand": (
        'Scalar.InstructionTyped [("%p", Scalar.RegisterType.integer .pred), '
        '("%r", Scalar.RegisterType.integer .u32), ("%f", Scalar.RegisterType.floating .f32)] [] 1 '
        '(Scalar.Instr.setpGt .f32 "%p" (.reg "%r") (.reg "%f"))'
    ),
    "float_compare_integer_right_operand": (
        'Scalar.InstructionTyped [("%p", Scalar.RegisterType.integer .pred), '
        '("%r", Scalar.RegisterType.integer .u32), ("%f", Scalar.RegisterType.floating .f32)] [] 1 '
        '(Scalar.Instr.setpGt .f32 "%p" (.reg "%f") (.reg "%r"))'
    ),
    "moe_combine_reads_output_instead_of_expert_plane": (
        '(Generated.moe_combine.program[38]?.map (fun instruction => match instruction with '
        '| .load _ _ _ address => address.base == Operand.reg "%yp" | _ => false)) = some true'
    ),

    "moe_route_last_gate_word_wrap": "((2^64-4)+8 : Nat) ≤ 2^64",
    "moe_live_gate_route_overlap": "Scalar.WordsDisjoint 128 6 128 3",
    "moe_route_partial_word_publication": (
        '(⟨.global,139⟩ : ISA.Location) ∈ MoeRouteStreamTests.shortDomain'
    ),

    "moe_expert_back_edge_as_matmul_pc": (
        '(Generated.moe_experts.program[54]?.map (fun instruction => match instruction with '
        '| .integer (.jump target) => target | _ => 0)) = some 32'
    ),
    "moe_expert_loop_without_route_query": "MoeExpertsLoopTests.one.core.queries = 0",

    "moe_expert_second_branch_skips_plane_steps": "MoeExperts.selectSteps 1 = 4",
    "moe_expert_second_plane_output_as_first": (
        '(MoeExperts.threadLayout MoeExpertsThreadTests.input MoeExpertsThreadTests.ctx 1 '
        '(MoeExpertsThreadTests.addresses 1 (by decide))).output = 288'
    ),
    "moe_expert_route_last_byte_wrap": "((2^64-2)+3 : Nat) < 2^64",
    "moe_expert_live_route_output_overlap": "Scalar.WordsDisjoint 128 3 128 18",
    "moe_expert_live_x_output_overlap": "Scalar.WordsDisjoint 0 6 0 18",
    "moe_expert_second_plane_undersized": "(4*((1*3+2)*3+2)+3 : Nat) < 4*(3*3)",
    "moe_expert_partial_h_publication": (
        '(⟨.global,259⟩ : ISA.Location) ∈ MoeExpertsStreamTests.shortDomain'
    ),
    "u32_wrong_high_byte_accepted": (
        '(match Scalar.u32Byte (2^24) 3 with | .bits value => some value | _ => none) = some (ISA.byte 0)'
    ),
    "moe_combine_live_h_y_overlap": "Scalar.WordsDisjoint 256 18 256 9",
    "moe_combine_live_r_y_overlap": "Scalar.WordsDisjoint 128 3 128 9",
    "moe_combine_h_word_last_byte_wrap": "((2^64-2)+3 : Nat) < 2^64",
    "moe_pipeline_combine_before_expert": (
        '(MoePipeline.commands MoePipelineTests.cfg).map (fun inv => inv.code.length) = [23,41,57]'
    ),
    "moe_pipeline_initial_r_already_selected": (
        '(match MoePipelineTests.heap 132 with | .bits value => some value | _ => none) = some (ISA.byte 1)'
    ),
    "moe_pipeline_initial_h_already_represented": (
        '(match MoePipelineTests.heap 304 with | .realPart _ _ _ => true | _ => false) = true'
    ),
    "moe_pipeline_initial_y_already_represented": (
        '(match MoePipelineTests.heap 396 with | .realPart _ _ _ => true | _ => false) = true'
    ),
    "moe_combine_partial_y_publication": (
        '(⟨.global,387⟩ : ISA.Location) ∈ MoeCombineMemoryTests.shortDomain'
    ),
    "mma_a_high_k_mistaken_for_high_row": (
        '(Ampere.Mma.aCoord (0,4)).1.val = 8'
    ),
    "mma_b_high_k_omitted": (
        '(Ampere.Mma.bCoord (0,2)).1.val = 0'
    ),
    "mma_accumulator_high_row_omitted": (
        '(Ampere.Mma.cCoord (0,2)).1.val = 0'
    ),
    "packed_f16_accepts_integer_bits": (
        '(Ampere.PackedF16.decode ((ISA.encodeU32 7).map ISA.Symbolic.Byte.bits)).isSome = true'
    ),
    "async_copy_source_queries_forget_issue": (
        '(CpAsyncCopyGraph.trace 64 128 CpAsyncCopyMemoryTests.bytes CpAsyncCopyMemoryTests.answers).final.scalar.core.queries = 4'
    ),
    "async_copy_payload_truncated_to_word": (
        'CpAsyncCopyMemoryTests.bytes.length = 4'
    ),
    "async_barrier_source_loses_async_pc_slots": (
        'Ampere.sourcePC AmpereTests.good Generated.cp_async_copy.program AmpereTests.params ISA.Dim3.one (AmpereTests.event 3) = some 3'
    ),
    "async_divergent_same_generation_sources_equal": (
        'Ampere.sourcePC AmpereOriginsTests.bad AmpereOriginsTests.badCode [] AmpereOriginsTests.geometry.block (AmpereOriginsTests.event AmpereOriginsTests.left 1) = Ampere.sourcePC AmpereOriginsTests.bad AmpereOriginsTests.badCode [] AmpereOriginsTests.geometry.block (AmpereOriginsTests.event AmpereOriginsTests.right 1)'
    ),
    "async_issuer_mistaken_for_copy_agent": (
        'Ampere.Node.agent (.copyWrite AmpereTests.operation) = Ampere.Node.agent (.thread (AmpereTests.event 0))'
    ),
    "different_copies_mistaken_for_one_agent": (
        'Ampere.Node.agent (.copyWrite (AmpereTests.opId 0)) = Ampere.Node.agent (.copyWrite (AmpereTests.opId 1))'
    ),
    "ampere_cg_short_copy": "Ampere.CopySize .cg 4",
    "ampere_invalid_wait_count": "Ampere.InstructionTyped [] [] 1 (.wait 8)",
    "ampere_fixed_copy_width_erased": (
        '(Generated.cp_async_copy.program[2]?.map (fun i => match i with | .copy _ _ _ size => size | _ => 0)) = some 8'
    ),
    "ampere_wait_one_drains_recent": (
        '(match AmpereTests.groups.eventAt (AmpereTests.event 5) with | some (.wait count keep) => some (count-keep) | _ => none) = some 2'
    ),
    "ampere_wait_zero_commits_open": (
        '(match AmpereTests.groups.eventAt (AmpereTests.event 6) with | some (.wait count keep) => some (count-keep) | _ => none) = some 3'
    ),
    "ampere_commit_is_wait": (
        '(match AmpereTests.good.eventAt (AmpereTests.event 1) with | some (.wait _ _) => true | _ => false) = true'
    ),
    "ampere_short_payload_accepted": (
        '(Ampere.run AmpereTests.ctx AmpereTests.shortOracle Generated.cp_async_copy.program 3 {}).toOption.isSome = true'
    ),

}


def run(args, cwd=ROOT):
    return subprocess.run(args, cwd=cwd, text=True, check=True)


def check_generated(directory):
    for name, module in CASES.items():
        output = directory / f"{module}.lean"
        run([
            "cargo", "run", "--quiet", "--locked", "--",
            f"examples/{name}.ptx", str(output),
        ])
        expected = LEAN / "Ptx" / "Generated" / f"{module}.lean"
        if output.read_bytes() != expected.read_bytes():
            raise SystemExit(f"Stale generated AST: {expected}; regenerate and review it")


def check_proofs():
    # Scan project sources; public theorem dependencies are audited separately.
    authored = set()
    for source in (LEAN / "Ptx").rglob("*.lean"):
        code = re.sub(r"/-.*?-/|--[^\n]*", "", source.read_text(), flags=re.S)
        if re.search(r"\bsorry\b|^\s*(axiom|constant|unsafe|partial)\b", code, flags=re.M):
            raise SystemExit(f"Untrusted proof construct in {source}")
        authored.update(re.findall(r"^(?:@\[[^\n]*\]\s*)?theorem\s+([\w.]+)", code, flags=re.M))

    run(["lake", "build", "Ptx", "Ptx.Tests"], LEAN)
    audit = subprocess.run(
        ["lake", "env", "lean", "Ptx/Tests/Audit.lean"],
        cwd=LEAN, text=True, capture_output=True,
    )
    if audit.returncode:
        raise SystemExit(f"Lean audit failed:\n{audit.stdout}\n{audit.stderr}")
    for names in re.findall(r"depends on axioms: \[([^\]]*)\]", audit.stdout):
        used = {name.strip() for name in names.split(",") if name.strip()}
        if used - ALLOWED_AXIOMS:
            raise SystemExit(f"Unapproved axiom: {used - ALLOWED_AXIOMS}")
    exported = set(re.findall(r"^PUBLIC_THEOREM (.+)$", audit.stdout, flags=re.M))
    audited = set(re.findall(r"^'([^']+)'", audit.stdout, flags=re.M))
    if not exported:
        raise SystemExit("Lean public theorem inventory is empty")
    required = {name for name in exported if any(name.endswith('.' + short) for short in authored)}
    if missing := required - audited:
        raise SystemExit(f"Public theorem dependency audit missing: {sorted(missing)}")
    print(f"Lean audit: {len(audited)} declarations checked; {len(required)} environment-resolved public theorem names covered")


def check_rejections(directory):
    imports = "\n".join([
        "import Ptx.Tests.ShuffleControl",
        "import Ptx.Tests.ShuffleUniversal",
        "import Ptx.Tests.ShuffleProbe",
        "import Ptx.Tests.Kernels",
        "import Ptx.Tests.Typing",
        "import Ptx.Tests.Scalar",
        "import Ptx.Tests.ScalarMatmulInit",
        "import Ptx.Tests.AtomicDispatch",
        "import Ptx.Tests.ScalarAttentionOuter",
        "import Ptx.Tests.ScalarAttentionEntry",
        "import Ptx.Tests.ScalarAttentionMemory",
        "import Ptx.Tests.SourceOrigins",
        "import Ptx.Tests.ScalarSourceOrigins",
        "import Ptx.Tests.Stream",
        "import Ptx.Tests.MoeRouteStream",
        "import Ptx.Tests.MoeExpertsLoop",
        "import Ptx.Tests.MoeExpertsThread",
        "import Ptx.Tests.MoeExpertsStream",
        "import Ptx.Tests.MoeExpertsBoundary",
        "import Ptx.Tests.MoeCombineMemory",
        "import Ptx.Tests.MoePipelineBoundary",
        "import Ptx.Tests.Ampere",
        "import Ptx.Ampere.Memory",
        "import Ptx.Tests.AmpereOrigins",
        "import Ptx.Tests.CpAsyncCopyMemory",
        "import Ptx.Tests.MmaFragments",
        "import Ptx.Tests.MmaLocal",
        "import Ptx.Tests.MemoryGraphRanked",
        "import Ptx.Tests.AmpereTiled",
        "import Ptx.Tests.AmpereTiledSpec",
        "import Ptx.Tests.AmpereTiledStage",
        "import Ptx.Tests.AmpereTiledLoop",
        "import Ptx.Tests.AmpereTiledSource",
        "import Ptx.Tests.AmpereTiledReconstruction",
        "import Ptx.Tests.AmpereTiledPhase",
        "import Ptx.Tests.AmpereTiledMemory",
        "import Ptx.Tests.AmpereTiledCorrect",
        "import Ptx.Tests.AmpereTiledWitness",
        "import Ptx.Tests.AmpereTiledWitnessMemory",
        "import Ptx.Tests.HopperMbarrier",
        "import Ptx.Tests.HopperResourceCycle",
        "import Ptx.Tests.Tma",
        "import Ptx.Tests.TmaInputValues",
        "import Ptx.Tests.TmaPhases",
        "import Ptx.Tests.TmaEligibility",
        "import Ptx.Tests.TmaInputCausal",
        "import Ptx.Tests.TmaRaces",
        "import Ptx.Tests.TmaConsumerChecked",
        "import Ptx.Tests.WgmmaSource",
        "import Ptx.Tests.WgmmaTensorSource",
        "import Ptx.Tests.Unified",
        "import Ptx.Tests.HopperStage",
        "import Ptx.Tests.UnifiedSchedules",
        "import Ptx.Tests.HopperStageAdmission",
        "import Ptx.Tests.UnifiedMemory",
        "import Ptx.Tests.HopperStageMemoryWitness",
        "import Ptx.Tests.HopperNativeControl",
        "import Ptx.Tests.HopperDoubleBuffer",
        "import Ptx.Tests.HopperDoubleBufferControl",
        "import Ptx.Tests.HopperDoubleBufferLoopControl",
        "import Ptx.Tests.HopperDoubleBufferIteration",
        "import Ptx.Tests.HopperDoubleBufferKernelLoop",
        "import Ptx.Tests.HopperDoubleBufferComplete",
        "import Ptx.Tests.HopperDoubleBufferData",
        "import Ptx.Tests.HopperDoubleBufferIndices",
        "import Ptx.Tests.HopperDoubleBufferResources",
        "import Ptx.Tests.HopperDoubleBufferResourceOrder",
        "import Ptx.Tests.HopperDoubleBufferResourceAdmission",
        "import Ptx.Tests.HopperDoubleBufferControlAdmission",
        "import Ptx.Tests.HopperDoubleBufferNativePublication",
        "import Ptx.Tests.HopperDoubleBufferNativeControl",
        "import Ptx.Tests.HopperDoubleBufferMemoryPhases",
        "import Ptx.Tests.HopperDoubleBufferEligibility",
        "import Ptx.Tests.HopperDoubleBufferMemoryWitness",
        "import Ptx.Tests.HopperDoubleBufferObservedOutput",
        "import Ptx.Tests.Shift",
        "import Ptx.Ampere.TiledLayout",
        "import Ptx.Generated.MoeCombine",
        "import Ptx.Tests.BarrierSites",
        "import Ptx.Tests.SharedSwap",
        "import Ptx.Tests.CopyEvent",
        "import Ptx.Tests.Termination",
        "import Ptx.Tests.SharedEvent",
        "import Ptx.Tests.SharedRefinement",
        "import Ptx.Tests.ByteProtocol",
        "import Ptx.Tests.ByteContents",
        "import Ptx.Tests.ByteContentsFootprint",
        "import Ptx.Tests.ByteValuePipeline",
        "import Ptx.Tests.ShuffleOutput",
        "import Ptx.Tests.Ordered",
        "import Ptx.Async.Contracts",
        "open Ptx Ptx.Examples",
    ])
    propositions = {
        name: f"({expression}).toOption.isSome = true"
        for name, expression in NEGATIVE_CASES.items()
    } | NEGATIVE_PROPOSITIONS
    check_decide_rejections(directory, imports, propositions)


def check_decide_rejections(directory, imports, propositions):
    # Every assertion remains a separate Lean command. Check the JSON diagnostic
    # at that command's own line, rather than accepting any failed Lean process.
    # Batch imports once; never count a parse/type/import error as a refutation.
    path = directory / "Reject.lean"
    source = f"{imports}\n"
    expected = {}
    for name, proposition in propositions.items():
        expected[source.count("\n") + 1 + proposition.count("\n")] = name
        source += f"example : {proposition} := by decide\n"
    path.write_text(source)
    result = subprocess.run(
        ["lake", "env", "lean", f"-DmaxErrors={len(propositions) + 10}", "-DmaxRecDepth=50000", "--json", str(path)],
        cwd=LEAN, text=True, capture_output=True,
    )
    if result.returncode != 1 or result.stderr.strip():
        raise SystemExit(f"Wrong rejection process result:\n{result.stdout}\n{result.stderr}")
    rejected = set()
    for line in result.stdout.splitlines():
        try:
            diagnostic = json.loads(line)
        except json.JSONDecodeError as error:
            raise SystemExit(f"Non-JSON rejection diagnostic: {line}") from error
        if diagnostic.get("severity") != "error":
            continue
        number = diagnostic.get("pos", {}).get("line")
        message = diagnostic.get("data", "")
        if (number not in expected or number in rejected
                or diagnostic.get("fileName") != str(path)
                or not message.startswith("Tactic `decide` proved that the proposition\n")
                or not message.endswith("is false")):
            raise SystemExit(f"Wrong rejection diagnostic: {diagnostic}")
        rejected.add(number)
    if rejected != expected.keys():
        missing = [name for number, name in expected.items() if number not in rejected]
        raise SystemExit(f"Missing evaluated refutations: {missing}")
    for name in propositions:
        print(f"Rejected by Lean: {name}")


def check_ptx(directory):
    ptxas = os.environ.get("PTXAS") or shutil.which("ptxas")
    if not ptxas:
        print("Skipping PTX assembly; set PTXAS to enable it")
        return
    targets, hashes = {}, {}
    for name in CASES:
        source = ROOT / f"examples/{name}.ptx"
        target = re.search(r"^\.target\s+(sm_[A-Za-z0-9]+)\s*$", source.read_text(), re.M)
        if not target or target[1] not in {"sm_70", "sm_80", "sm_90a"}:
            raise SystemExit(f"Unsupported assembly target in {source}")
        targets[name] = target[1]
        run([ptxas, f"-arch={target[1]}", str(source), "-o", str(directory / f"{name}.cubin")])
        hashes[name] = hashlib.sha256(source.read_bytes()).hexdigest()
    report = {
        "schema_version": 1,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "status": "passed",
        "tool_version": subprocess.check_output([ptxas, "--version"], text=True).strip(),
        "target": "per-fixture sm_70/sm_80/sm_90a",
        "targets": targets,
        "scope": "assembly syntax/target validation only; no execution, convergence or memory-safety verdict",
        "fixtures": hashes,
    }
    (ROOT / "docs/assembly-evidence.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PTX assembly: {len(CASES)} examples accepted; source-hashed report updated")


def main():
    check_coverage()
    with tempfile.TemporaryDirectory(prefix="ptx-verify-") as temporary:
        directory = Path(temporary)
        check_generated(directory)
        check_proofs()
        check_rejections(directory)
        check_ptx(directory)
    print("All verifier checks passed")


if __name__ == "__main__":
    main()
