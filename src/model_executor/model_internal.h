#ifndef VI_MODEL_INTERNAL_H
#define VI_MODEL_INTERNAL_H

#include "verifiedinfer/model_executor/model.h"

/* Small operator boundary; no graph framework or public generic Tensor type.
 * All dimensions are checked before these routines. Inputs/outputs are disjoint
 * except residual and SiLU updates explicitly described by their signatures. */
typedef struct {
    vi_status (*create)(void **context);
    void (*destroy)(void *context);
    float *(*allocate)(void *context, size_t count);
    void (*release)(float *data);
    vi_status (*write)(void *, float *, const float *, size_t);
    vi_status (*read)(void *, float *, const float *, size_t);
    vi_status (*copy)(void *, float *, const float *, size_t);
    vi_status (*linear)(void *, const float *, const float *, const float *, float *, size_t, size_t);
    vi_status (*norm)(void *, const float *, const float *, float *, size_t, float);
    vi_status (*rope)(void *, float *, size_t, size_t, size_t, float);
    vi_status (*attention)(void *, const float *, const float *, const float *, float *, float *,
                           size_t, size_t, size_t, size_t, size_t);
    vi_status (*add)(void *, float *, const float *, size_t);
    vi_status (*swiglu)(void *, float *, const float *, size_t);
} vi_model_ops;

typedef struct {
    const float *input_norm, *q, *k, *v, *o;
    const float *q_bias, *k_bias, *v_bias, *o_bias;
    const float *post_norm, *gate, *up, *down;
} vi_layer_weights;

typedef struct {
    char name[192];
    float *data;
    size_t rows, cols;
    bool used;
} vi_loaded_tensor;

struct vi_model {
    vi_model_config config;
    vi_device device;
    const vi_model_ops *ops;
    vi_loaded_tensor *tensors;
    size_t tensor_count;
    vi_layer_weights *layers;
    const float *embedding, *output_norm, *lm_head;
};

struct vi_model_state {
    const vi_model *model;
    void *context;
    float *keys, *values, *workspace;
    size_t capacity, cached_tokens;
    bool failed;
};

#ifdef __cplusplus
extern "C" {
#endif
const vi_model_ops *vi_cpu_model_ops(void);
const vi_model_ops *vi_cuda_model_ops(void);
#ifdef __cplusplus
}
#endif

#endif
