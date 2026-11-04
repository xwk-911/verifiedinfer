#include "../model_internal.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

static vi_status forward(void *opaque, const vi_model_input *input, float *logits, size_t vocab)
{
    vi_model_state *s = opaque;
    if (s == NULL || input == NULL || input->tokens == NULL || logits == NULL || input->count == 0)
        return VI_INVALID;
    if (s->failed) return VI_MODEL_ERROR;
    const vi_model *model = s->model;
    const vi_model_config *c = &model->config;
    if (vocab != c->vocab_size || input->position != s->cached_tokens) return VI_INVALID;
    if (input->count > s->capacity - s->cached_tokens) return VI_NO_SPACE;
    for (size_t t = 0; t < input->count; ++t)
        if (input->tokens[t] >= vocab) return VI_INVALID;
    const vi_model_ops *ops = model->ops;
    void *ctx = s->context;
    const size_t d = c->hidden_size, f = c->intermediate_size;
    const size_t q_width = c->num_heads * c->head_dim, kv_width = c->num_kv_heads * c->head_dim;
    float *x = s->workspace, *n = x + d, *projected = n + d;
    float *q = projected + d, *attended = q + q_width;
    float *gate = attended + q_width, *up = gate + f;
    float *scores = up + f, *device_logits = scores + c->num_heads * s->capacity;
    /* Only commit cache length after all kernels, copies and finite checks.
     * Any compute error poisons the state; no assumption of GPU rollback. */
#define RUN(call) do { if ((call) != VI_OK) { s->failed = true; return VI_MODEL_ERROR; } } while (0)
    for (size_t t = 0; t < input->count; ++t) {
        const size_t p = input->position + t;
        RUN(ops->copy(ctx, x, model->embedding + (size_t)input->tokens[t] * d, d));
        for (size_t layer = 0; layer < c->num_layers; ++layer) {
            const vi_layer_weights *w = &model->layers[layer];
            float *keys = s->keys + layer * s->capacity * kv_width;
            float *values = s->values + layer * s->capacity * kv_width;
            RUN(ops->norm(ctx, x, w->input_norm, n, d, c->rms_norm_epsilon));
            RUN(ops->linear(ctx, w->q, w->q_bias, n, q, q_width, d));
            RUN(ops->linear(ctx, w->k, w->k_bias, n, keys + p * kv_width, kv_width, d));
            RUN(ops->linear(ctx, w->v, w->v_bias, n, values + p * kv_width, kv_width, d));
            RUN(ops->rope(ctx, q, c->num_heads, c->head_dim, p, c->rope_theta));
            RUN(ops->rope(ctx, keys + p * kv_width, c->num_kv_heads, c->head_dim, p, c->rope_theta));
            RUN(ops->attention(ctx, q, keys, values, attended, scores, c->num_heads,
                               c->num_kv_heads, c->head_dim, p + 1, s->capacity));
            RUN(ops->linear(ctx, w->o, w->o_bias, attended, projected, d, q_width));
            RUN(ops->add(ctx, x, projected, d));
            RUN(ops->norm(ctx, x, w->post_norm, n, d, c->rms_norm_epsilon));
            RUN(ops->linear(ctx, w->gate, NULL, n, gate, f, d));
            RUN(ops->linear(ctx, w->up, NULL, n, up, f, d));
            RUN(ops->swiglu(ctx, gate, up, f));
            RUN(ops->linear(ctx, w->down, NULL, gate, projected, d, f));
            RUN(ops->add(ctx, x, projected, d));
        }
    }
    RUN(ops->norm(ctx, x, model->output_norm, n, d, c->rms_norm_epsilon));
    RUN(ops->linear(ctx, model->lm_head, NULL, n, device_logits, vocab, d));
    RUN(ops->read(ctx, logits, device_logits, vocab));
#undef RUN
    for (size_t i = 0; i < vocab; ++i) {
        if (!isfinite(logits[i])) { s->failed = true; return VI_MODEL_ERROR; }
    }
    s->cached_tokens += input->count;
    return VI_OK;
}

static int add_product(size_t *n, size_t a, size_t b)
{
    const size_t limit = SIZE_MAX / sizeof(float);
    if (a == 0 || b == 0 || a > limit / b || *n > limit - a * b) return 0;
    *n += a * b;
    return 1;
}

vi_status vi_model_state_create(const vi_model *model, size_t capacity,
                                vi_model_state **out, vi_model_runner *runner,
                                char *error, size_t error_capacity)
{
    const char *why = "invalid model or context capacity";
    vi_model_state *s = NULL;
    if (model == NULL || out == NULL || runner == NULL || capacity == 0 ||
        capacity > model->config.max_seq_len) goto fail;
    const vi_model_config *c = &model->config;
    size_t cache_count = 0, workspace_count = 0, per_layer = 0;
    if (!add_product(&per_layer, capacity, c->num_kv_heads * c->head_dim) ||
        !add_product(&cache_count, c->num_layers, per_layer) ||
        !add_product(&workspace_count, 3, c->hidden_size) ||
        !add_product(&workspace_count, 2, c->num_heads * c->head_dim) ||
        !add_product(&workspace_count, 2, c->intermediate_size) ||
        !add_product(&workspace_count, c->num_heads, capacity) ||
        !add_product(&workspace_count, 1, c->vocab_size)) goto fail;
    why = "unable to allocate model state/device resources";
    s = calloc(1, sizeof(*s));
    if (s == NULL) goto fail;
    s->model = model;
    s->capacity = capacity;
    if (model->ops->create(&s->context) != VI_OK) goto fail;
    s->keys = model->ops->allocate(s->context, cache_count);
    s->values = model->ops->allocate(s->context, cache_count);
    s->workspace = model->ops->allocate(s->context, workspace_count);
    if (s->keys == NULL || s->values == NULL || s->workspace == NULL) goto fail;
    *runner = (vi_model_runner){.model = s, .forward = forward, .vocab_size = c->vocab_size};
    *out = s;
    return VI_OK;
fail:
    vi_model_state_free(s);
    if (error != NULL && error_capacity != 0) snprintf(error, error_capacity, "%s", why);
    return VI_INVALID;
}

size_t vi_model_cached_tokens(const vi_model_state *state) { return state ? state->cached_tokens : 0; }
void vi_model_state_free(vi_model_state *s)
{
    if (s == NULL) return;
    s->model->ops->destroy(s->context);
    s->model->ops->release(s->keys);
    s->model->ops->release(s->values);
    s->model->ops->release(s->workspace);
    free(s);
}
const vi_model_config *vi_model_get_config(const vi_model *model) { return model ? &model->config : NULL; }
