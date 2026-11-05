#include "model_internal.h"
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

int vi_model_problem(vi_diagnostic e, const char *format, ...)
{
    if (e.text != NULL && e.size != 0) {
        va_list args;
        va_start(args, format);
        vsnprintf(e.text, e.size, format, args);
        va_end(args);
    }
    return 0;
}
vi_status vi_model_load(const char *directory, vi_device device, vi_model **out,
                        char *error, size_t capacity)
{
    vi_diagnostic e = {error, capacity};
    if (error && capacity) error[0] = 0;
    if (directory == NULL || out == NULL || (device != VI_DEVICE_CPU && device != VI_DEVICE_CUDA)) {
        vi_model_problem(e, "invalid load arguments"); return VI_INVALID;
    }
    vi_model *m = calloc(1, sizeof(*m));
    if (m == NULL) { vi_model_problem(e, "model allocation failed"); return VI_INVALID; }
    m->ops = vi_cpu_model_ops();
    if (!vi_model_checkpoint_load(m, directory, e)) goto fail;
    if (device == VI_DEVICE_CUDA) {
#ifdef VI_ENABLE_CUDA
        const vi_model_ops *cuda = vi_cuda_model_ops();
        void *context = NULL;
        if (cuda->create(&context) != VI_OK) { vi_model_problem(e, "CUDA initialization failed"); goto fail; }
        /* Stage all uploads, then switch ownership so failure cleanup is exact. */
        float **uploaded = calloc(m->tensor_count, sizeof(*uploaded));
        bool success = uploaded != NULL;
        for (size_t i = 0; success && i < m->tensor_count; ++i) {
            size_t count = m->tensors[i].rows * m->tensors[i].cols;
            uploaded[i] = cuda->allocate(context, count);
            success = uploaded[i] != NULL && cuda->write(context, uploaded[i], m->tensors[i].data, count) == VI_OK;
        }
        cuda->destroy(context);
        if (!success) {
            if (uploaded) for (size_t i = 0; i < m->tensor_count; ++i) cuda->release(uploaded[i]);
            free(uploaded); vi_model_problem(e, "CUDA weight upload failed"); goto fail;
        }
        m->implementation->executor->free_weights(m->weights); m->weights = NULL;
        for (size_t i = 0; i < m->tensor_count; ++i) {
            free(m->tensors[i].data); m->tensors[i].data = uploaded[i];
        }
        free(uploaded); m->ops = cuda; m->device = device;
        /* Metadata and tied-weight equality were validated before upload. */
        if (!m->implementation->executor->bind_weights(m, e)) goto fail;
#else
        vi_model_problem(e, "CUDA not built; use make CUDA=1 or select --device cpu"); goto fail;
#endif
    }
    *out = m;
    return VI_OK;
fail:
    vi_model_free(m);
    return VI_INVALID;
}

void vi_model_free(vi_model *model)
{
    if (model == NULL) return;
    if (model->implementation != NULL)
        model->implementation->executor->free_weights(model->weights);
    for (size_t i = 0; i < model->tensor_count; ++i)
        model->ops->release(model->tensors[i].data);
    free(model->tensors);
    free(model);
}

const vi_model_config *vi_model_get_config(const vi_model *model)
{
    return model ? &model->config : NULL;
}

vi_status vi_model_state_create(const vi_model *model, size_t capacity,
                                vi_model_state **out, vi_model_runner *runner,
                                char *error, size_t error_capacity)
{
    vi_diagnostic diagnostic = {error, error_capacity};
    if (model == NULL || out == NULL || runner == NULL || capacity == 0 ||
        capacity > model->config.max_seq_len) {
        vi_model_problem(diagnostic, "invalid model or context capacity");
        return VI_INVALID;
    }
    vi_model_state *state = calloc(1, sizeof(*state));
    if (state == NULL) {
        vi_model_problem(diagnostic, "unable to allocate model state");
        return VI_INVALID;
    }
    state->model = model;
    state->capacity = capacity;
    vi_status status = model->implementation->executor->create_state(
        model, capacity, &state->data, error, error_capacity);
    if (status != VI_OK) { free(state); return status; }
    vi_model_runner_bind(state, runner);
    *out = state;
    return VI_OK;
}

size_t vi_model_cached_tokens(const vi_model_state *state)
{
    return state ? state->model->implementation->executor->computed_tokens(state->data) : 0;
}

void vi_model_state_free(vi_model_state *state)
{
    if (state == NULL) return;
    state->model->implementation->executor->free_state(state->data);
    free(state);
}
