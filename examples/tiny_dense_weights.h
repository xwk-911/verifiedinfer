#ifndef VI_TINY_DENSE_WEIGHTS_H
#define VI_TINY_DENSE_WEIGHTS_H

#include "verifiedinfer/model_executor/models/dense_model.h"

/* Deterministic, UNTRAINED fixture, deliberately using a vocabulary > 32.
 * These are test weights, not a model download or a text-generation demo. */
enum {
    TINY_VOCAB = 40, TINY_HIDDEN = 4, TINY_FFN = 6, TINY_CONTEXT = 8,
    TINY_WEIGHTS = 2 * TINY_VOCAB * TINY_HIDDEN + TINY_CONTEXT * TINY_HIDDEN +
        3 * TINY_HIDDEN + 4 * TINY_HIDDEN * TINY_HIDDEN + 3 * TINY_FFN * TINY_HIDDEN,
    TINY_KV = TINY_CONTEXT * TINY_HIDDEN,
    TINY_WORKSPACE = 5 * TINY_HIDDEN + 2 * TINY_FFN + TINY_CONTEXT
};

static inline vi_status tiny_dense_weights_init(vi_dense_weights *weights,
                                               float storage[TINY_WEIGHTS])
{
    const vi_dense_config config = {.vocab_size = TINY_VOCAB,
        .hidden_size = TINY_HIDDEN, .intermediate_size = TINY_FFN,
        .max_seq_len = TINY_CONTEXT, .rms_norm_epsilon = 1e-5f};
    for (size_t i = 0; i < TINY_WEIGHTS; ++i) {
        storage[i] = (float)((int)((i * 37 + 11) % 101) - 50) / 128.0f;
    }
    vi_status status = vi_dense_weights_init(weights, config, storage, TINY_WEIGHTS);
    if (status != VI_OK) {
        return status;
    }
    /* Finish constructing the fixture before lending it to any model. */
    const size_t norm_offsets[] = {
        (size_t)(weights->attention_norm - storage),
        (size_t)(weights->ffn_norm - storage),
        (size_t)(weights->output_norm - storage)
    };
    for (size_t i = 0; i < 3; ++i) {
        for (size_t j = 0; j < TINY_HIDDEN; ++j) {
            storage[norm_offsets[i] + j] = 1.0f;
        }
    }
    return VI_OK;
}

#endif
