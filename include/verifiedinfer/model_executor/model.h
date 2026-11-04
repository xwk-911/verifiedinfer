#ifndef VI_MODEL_H
#define VI_MODEL_H

#include <stdbool.h>
#include "verifiedinfer/model_executor/model_runner.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef enum { VI_DEVICE_CPU, VI_DEVICE_CUDA } vi_device;
typedef enum { VI_ARCH_LLAMA, VI_ARCH_QWEN2 } vi_model_architecture;

/* Normalized capabilities, not a model-name whitelist. Full causal attention,
 * half-split RoPE, RMSNorm and SwiGLU only. All runtime tensors are FP32. */
typedef struct {
    vi_model_architecture architecture;
    size_t vocab_size, hidden_size, intermediate_size, num_layers;
    size_t num_heads, num_kv_heads, head_dim, max_seq_len;
    float rms_norm_epsilon, rope_theta;
    bool qkv_bias, attention_output_bias, tie_embeddings;
} vi_model_config;

typedef struct vi_model vi_model;             /* Immutable resident weights. */
typedef struct vi_model_state vi_model_state; /* Exclusive KV and workspace. */

/* config.json + model.safetensors or model.safetensors.index.json. Checks shape,
 * dtype, bounds and supported features. Failure leaves *out unchanged and writes
 * a diagnostic if error/error_capacity are provided. No remote code execution.
 * F32, BF16 and F16 checkpoint weights are converted to FP32 without quantizing.
 * CUDA support is optional at build time. These routines allocate resources. */
vi_status vi_model_load(const char *directory, vi_device device, vi_model **out,
                        char *error, size_t error_capacity);
const vi_model_config *vi_model_get_config(const vi_model *model);
void vi_model_free(vi_model *model);

/* The model outlives all states and runners borrowing it. Separate states may
 * share weights; do not call a state concurrently. context <= model max length.
 * Initialization returns an empty-cache runner, without changing the engine API.
 * Fatal compute failures poison this state; create a new state before retrying.
 * Validation/capacity failures do not consume input. All calls are synchronous. */
vi_status vi_model_state_create(const vi_model *model, size_t context,
                                vi_model_state **out, vi_model_runner *runner,
                                char *error, size_t error_capacity);
size_t vi_model_cached_tokens(const vi_model_state *state);
void vi_model_state_free(vi_model_state *state);

#ifdef __cplusplus
}
#endif
#endif
