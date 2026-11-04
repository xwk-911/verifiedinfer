#ifndef VI_MOCK_MODEL_H
#define VI_MOCK_MODEL_H

#include "verifiedinfer/model_executor/model_runner.h"
#include "verifiedinfer/memory/token_buffer.h"

/* Test model only: cached token IDs stand in for K/V tensors. A rolling prefix
 * hash determines integer-valued logits. This is not a dense neural model. */
typedef struct {
    vi_token_buffer cache;
    uint32_t prefix_hash;
    size_t forward_calls;
} vi_mock_model;

/* Borrows exclusive token storage and returns a runner pointing at mock.
 * Model, runner and array are disjoint and outlive the engine using them.
 * No heap allocation; copying the runner does not copy its model state. */
vi_status vi_mock_model_init(vi_mock_model *mock, vi_token *cache_storage,
                               size_t capacity, size_t vocab_size,
                               vi_model_runner *model_runner);

#endif
