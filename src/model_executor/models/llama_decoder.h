#ifndef VI_LLAMA_DECODER_H
#define VI_LLAMA_DECODER_H
#include "../model_internal.h"

typedef struct {
    const float *input_norm, *q, *k, *v, *o;
    const float *q_bias, *k_bias, *v_bias, *o_bias;
    const float *post_norm, *gate, *up, *down;
} vi_layer_weights;

/* Private layout for the full-attention Llama/Qwen2 compatibility subset. */
typedef struct {
    vi_model_config config;
    const vi_model_ops *ops;
    vi_layer_weights *layers;
    const float *embedding, *output_norm, *lm_head;
} vi_llama_weights;

typedef struct {
    const vi_llama_weights *model;
    void *context;
    float *keys, *values, *workspace;
    size_t capacity, cached_tokens;
    bool failed;
} vi_llama_state;

extern const vi_model_executor vi_llama_executor;
#endif
