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
    char name[192];
    float *data;
    size_t rows, cols;
    bool used;
} vi_loaded_tensor;

typedef struct vi_json vi_json;
typedef struct { char *text; size_t size; } vi_diagnostic;

/* Architecture callbacks own their weight views and request-state layout.
 * The common model/runner never assumes that state is two dense KV arrays.
 * create_state cleans partial allocations on failure and publishes only on
 * success. The model outlives its states; forward follows model_runner.h. */
typedef struct {
    int (*configure)(vi_model *, const vi_json *, vi_diagnostic);
    int (*bind_weights)(vi_model *, vi_diagnostic);
    void (*free_weights)(void *);
    vi_status (*create_state)(const vi_model *, size_t, void **, char *, size_t);
    void (*free_state)(void *);
    vi_model_forward_fn forward;
    size_t (*computed_tokens)(const void *);
} vi_model_executor;

typedef struct {
    const char *architecture, *model_type;
    vi_model_architecture id;
    const vi_model_executor *executor;
} vi_model_implementation;

struct vi_model {
    vi_model_config config;
    vi_device device;
    const vi_model_ops *ops;
    const vi_model_implementation *implementation;
    vi_loaded_tensor *tensors;
    size_t tensor_count;
    void *weights;
};

struct vi_model_state {
    const vi_model *model;
    void *data;
    size_t capacity;
    bool failed;
};

#ifdef __cplusplus
extern "C" {
#endif
const vi_model_ops *vi_cpu_model_ops(void);
const vi_model_ops *vi_cuda_model_ops(void);
const vi_model_implementation *vi_model_registry_find(const char *, const char *);
int vi_model_checkpoint_load(vi_model *, const char *, vi_diagnostic);
int vi_model_problem(vi_diagnostic, const char *);
int vi_model_problem_string(vi_diagnostic, const char *, const char *);
int vi_model_problem_shape(vi_diagnostic, const char *, size_t, size_t, size_t, size_t);
void vi_model_layer_name(char *, size_t, const char *);
void vi_model_runner_bind(vi_model_state *, vi_model_runner *);
#ifdef __cplusplus
}
#endif
#endif
