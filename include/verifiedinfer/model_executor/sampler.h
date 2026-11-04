#ifndef VI_SAMPLER_H
#define VI_SAMPLER_H

#include "verifiedinfer/common/types.h"

typedef struct {
    vi_token token;
    uint32_t next_state;
} vi_sample_result;

/* Scaffold greedy sampler, not Vosti's production sampler. logits is readable;
 * result does not alias it. Maximum-score ties use a traversal starting at
 * state % vocab_size. Failure preserves result; input is never modified.
 * Rejects nonfinite logits and invalid vocabulary sizes. */
vi_status vi_sample_greedy(const float *logits, size_t vocab_size,
                           uint32_t state, vi_sample_result *result);

#endif
