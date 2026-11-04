#include "verifiedinfer/model_executor/sampler.h"

#include <math.h>

vi_status vi_sample_greedy(const float *logits, size_t vocab_size,
                           uint32_t state, vi_sample_result *result)
{
    if (logits == NULL || result == NULL || !vi_vocab_size_valid(vocab_size)) {
        return VI_INVALID;
    }
    for (size_t i = 0; i < vocab_size; ++i) {
        if (!isfinite(logits[i])) {
            return VI_INVALID;
        }
    }
    size_t best = state % vocab_size;
    size_t candidate = best;
    for (size_t i = 1; i < vocab_size; ++i) {
        candidate = candidate == vocab_size - 1 ? 0 : candidate + 1;
        if (logits[candidate] > logits[best]) {
            best = candidate;
        }
    }
    *result = (vi_sample_result){
        .token = (vi_token)best,
        .next_state = (uint32_t)(UINT64_C(1664525) * state + UINT64_C(1013904223))
    };
    return VI_OK;
}
