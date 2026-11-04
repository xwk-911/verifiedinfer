#ifndef VI_MODEL_RUNNER_H
#define VI_MODEL_RUNNER_H

#include "verifiedinfer/common/types.h"

typedef struct {
    const vi_token *tokens;
    size_t count;
    size_t position; /* Absolute start position; must equal cached token count. */
} vi_model_input;

/* Minimal model execution interface, inspired by DeepInfer's ModelRunner.
 * This combines decoder forward and LM-head projection into last-row logits.
 * Model state is exclusive to one request; immutable weights may be shared.
 * Input starts at the committed cache length, count > 0. Success consumes the
 * whole suffix and writes vocab_size finite logits. Failure preserves cache
 * length and its committed prefix; workspace, unused cache and logits may be
 * overwritten. No pointers are retained; all work completes before return.
 * Arrays, state descriptors and output do not alias. Callers provide actual
 * storage matching all declared capacities. These are obligations, not proofs. */
typedef vi_status (*vi_model_forward_fn)(void *model, const vi_model_input *input,
                                        float *logits, size_t vocab_size);

typedef struct {
    void *model;
    vi_model_forward_fn forward;
    size_t vocab_size;
} vi_model_runner;

#endif
