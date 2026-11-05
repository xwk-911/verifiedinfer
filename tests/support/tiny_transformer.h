#ifndef VI_TINY_TRANSFORMER_H
#define VI_TINY_TRANSFORMER_H

#include "verifiedinfer/model_executor/model_runner.h"

/* One layer, one attention head, learned absolute positions, no biases.
 * Dense SwiGLU FFN; this is a test architecture, not a checkpoint format. */
typedef struct {
    size_t vocab_size;
    size_t hidden_size;
    size_t intermediate_size;
    size_t max_seq_len;
    float rms_norm_epsilon;
} vi_tiny_transformer_config;

/* Immutable row-major weights. Matrices have shape [output, input].
 * Initialized as views into caller storage in the field order below.
 * Descriptor and backing storage outlive every model that borrows them. */
typedef struct {
    vi_tiny_transformer_config config;
    const float *token_embedding;    /* [vocab, hidden] */
    const float *position_embedding; /* [max_seq_len, hidden] */
    const float *attention_norm;     /* [hidden] */
    const float *q_proj;             /* [hidden, hidden] */
    const float *k_proj;
    const float *v_proj;
    const float *o_proj;
    const float *ffn_norm;           /* [hidden] */
    const float *gate_proj;          /* [intermediate, hidden] */
    const float *up_proj;
    const float *down_proj;          /* [hidden, intermediate] */
    const float *output_norm;        /* [hidden] */
    const float *lm_head;            /* [vocab, hidden] */
} vi_tiny_transformer_weights;

typedef struct {
    float *keys;   /* [capacity, hidden], committed prefix [0, len) */
    float *values;
    size_t len;
    size_t capacity; /* Tokens, not float elements. */
} vi_tiny_transformer_kv_cache;

typedef struct {
    const vi_tiny_transformer_weights *weights; /* Shared read-only. */
    vi_tiny_transformer_kv_cache cache;         /* Exclusive to this request. */
    float *workspace;               /* Exclusive temporary float elements. */
    size_t workspace_count;
} vi_tiny_transformer_model;

/* Required float-element counts, or zero for invalid/overflowing config. */
size_t vi_tiny_transformer_weights_count(vi_tiny_transformer_config config);
size_t vi_tiny_transformer_workspace_count(vi_tiny_transformer_config config);
size_t vi_tiny_transformer_kv_count(vi_tiny_transformer_config config); /* For EACH of K and V. */

/* Validates finite weights and creates immutable views; failure changes nothing. */
vi_status vi_tiny_transformer_weights_init(vi_tiny_transformer_weights *weights, vi_tiny_transformer_config config,
                                const float *storage, size_t count);

/* No allocation. Arrays/descriptors are disjoint, except immutable weights may
 * be shared by multiple models. weights must come from weights_init and remain
 * unchanged. A runner is a borrowed handle: copying it does not clone state.
 * On forward failure only the committed cache prefix and length are preserved;
 * scratch and unused cache rows may have changed. See model_runner.h. */
vi_status vi_tiny_transformer_model_init(vi_tiny_transformer_model *model, const vi_tiny_transformer_weights *weights,
                              float *keys, float *values, size_t kv_count,
                              float *workspace, size_t workspace_count,
                              vi_model_runner *runner);

#endif
