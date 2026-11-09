#include "llama_decoder.h"
#include "../model_json.h"
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int configure(vi_model *model, const vi_json *j, vi_diagnostic e)
{
    vi_model_config *c = &model->config;
    const vi_model_implementation *selected = model->implementation;
    int ok = 0;
    c->architecture = selected->id;
#define SIZE_FIELD(name, field) do { if (!vi_json_integer(j, vi_json_member(j, 0, name), &c->field) || c->field == 0 || c->field > INT_MAX) { vi_model_problem_string(e, "invalid config field ", name); goto done; } } while (0)
    SIZE_FIELD("vocab_size", vocab_size);
    SIZE_FIELD("hidden_size", hidden_size);
    SIZE_FIELD("intermediate_size", intermediate_size);
    SIZE_FIELD("num_hidden_layers", num_layers);
    SIZE_FIELD("num_attention_heads", num_heads);
    SIZE_FIELD("max_position_embeddings", max_seq_len);
#undef SIZE_FIELD
    int kv = vi_json_member(j, 0, "num_key_value_heads"), hd = vi_json_member(j, 0, "head_dim");
    c->num_kv_heads = c->num_heads;
    if (kv != -1 && !vi_json_integer(j, kv, &c->num_kv_heads)) goto invalid;
    if (c->hidden_size % c->num_heads != 0) goto invalid;
    c->head_dim = c->hidden_size / c->num_heads;
    if (hd != -1 && !vi_json_integer(j, hd, &c->head_dim)) goto invalid;
    if (c->num_kv_heads == 0 || c->num_heads % c->num_kv_heads != 0 ||
        c->head_dim == 0 || c->head_dim % 2 != 0 ||
        c->head_dim > (size_t)INT_MAX / c->num_heads ||
        c->num_layers > SIZE_MAX / sizeof(vi_layer_weights) ||
        !vi_vocab_size_valid(c->vocab_size)) goto invalid;
    c->rms_norm_epsilon = 1e-6f;
    int eps = vi_json_member(j, 0, "rms_norm_eps"), theta = vi_json_member(j, 0, "rope_theta");
    if (eps != -1 && !vi_json_number(j, eps, &c->rms_norm_epsilon)) goto invalid;
    c->rope_theta = 10000;
    if (theta != -1 && !vi_json_number(j, theta, &c->rope_theta)) goto invalid;
    if (c->rms_norm_epsilon <= 0 || c->rope_theta <= 0) goto invalid;
    if (!vi_json_boolean(j, "attention_bias", selected->id == VI_ARCH_QWEN2, &c->qkv_bias) ||
        !vi_json_boolean(j, "tie_word_embeddings", false, &c->tie_embeddings)) goto invalid;
    c->attention_output_bias = c->architecture == VI_ARCH_LLAMA && c->qkv_bias;
    if (c->architecture == VI_ARCH_QWEN2 && !c->qkv_bias) goto unsupported;
    bool flag;
    if (!vi_json_boolean(j, "mlp_bias", false, &flag) || flag ||
        !vi_json_boolean(j, "use_sliding_window", false, &flag) || flag ||
        !vi_json_boolean(j, "rope_interleaved", false, &flag) || flag ||
        !vi_json_boolean(j, "qk_norm", false, &flag) || flag ||
        !vi_json_absent_or_null(j, "rope_scaling") || !vi_json_absent_or_null(j, "rope_parameters") ||
        !vi_json_absent_or_null(j, "quantization_config")) goto unsupported;
    if (!vi_json_equal(j, vi_json_member(j, 0, "hidden_act"), "silu")) goto unsupported;
    int partial = vi_json_member(j, 0, "partial_rotary_factor");
    float fraction = 1;
    if (partial != -1 && (!vi_json_number(j, partial, &fraction) || fraction != 1)) goto unsupported;
    int layer_types = vi_json_member(j, 0, "layer_types");
    if (layer_types != -1 && !vi_json_equal(j, layer_types, "null")) {
        if (layer_types < 0 || j->tokens[layer_types].type != JSMN_ARRAY ||
            (size_t)j->tokens[layer_types].size != c->num_layers) goto unsupported;
        for (int i = layer_types + 1; i < vi_json_next(j, layer_types); ++i)
            if (!vi_json_equal(j, i, "full_attention")) goto unsupported;
    }
    if (c->architecture == VI_ARCH_LLAMA && !vi_json_absent_or_null(j, "sliding_window")) goto unsupported;
    ok = 1; goto done;
unsupported:
    vi_model_problem(e, "unsupported model features (requires full attention, unscaled half-split RoPE, SwiGLU, no quantization/QK norm)"); goto done;
invalid:
    vi_model_problem(e, "invalid attention geometry or model configuration");
done:
    return ok;
}
static const float *tensor(vi_model *m, const char *name, size_t rows, size_t cols, const vi_diagnostic *e)
{
    for (size_t i = 0; i < m->tensor_count; ++i) {
        vi_loaded_tensor *t = &m->tensors[i];
        if (strcmp(t->name, name) != 0) continue;
        if (t->rows != rows || t->cols != cols) {
            vi_model_problem_shape(*e, name, rows, cols, t->rows, t->cols);
            return NULL;
        }
        t->used = true;
        return t->data;
    }
    vi_model_problem_string(*e, "missing tensor: ", name);
    return NULL;
}
static int bind_layer_tensor(vi_model *m, char *buffer, size_t layer,
                             const char *suffix, size_t rows, size_t cols,
                             const float **slot, const vi_diagnostic *e)
{
    char *name = buffer + 1;
    vi_model_layer_name(name, layer, suffix);
    const float *data = tensor(m, name, rows, cols, e);
    *slot = data;
    return *slot != NULL;
}
static int bind_weights(vi_model *m, vi_diagnostic e)
{
    vi_llama_weights *weights = calloc(1, sizeof(*weights));
    if (weights == NULL) { int result = vi_model_problem(e, "weight view allocation failed"); return result; }
    m->weights = weights;
    weights->config = m->config;
    weights->ops = m->ops;
    const vi_model_config *c = &m->config;
    size_t d = c->hidden_size, f = c->intermediate_size;
    size_t q = c->num_heads * c->head_dim, kv = c->num_kv_heads * c->head_dim;
    weights->layers = calloc(c->num_layers, sizeof(*weights->layers));
    if (weights->layers == NULL) { int result = vi_model_problem(e, "layer allocation failed"); return result; }
    weights->embedding = tensor(m, "model.embed_tokens.weight", c->vocab_size, d, &e);
    weights->output_norm = tensor(m, "model.norm.weight", d, 1, &e);
    if (weights->embedding == NULL || weights->output_norm == NULL) return 0;
    weights->lm_head = c->tie_embeddings ? weights->embedding : tensor(m, "lm_head.weight", c->vocab_size, d, &e);
    if (weights->lm_head == NULL) return 0;
    if (c->tie_embeddings) {
        for (size_t i = 0; i < m->tensor_count; ++i) {
            vi_loaded_tensor *t = &m->tensors[i];
            int head_name_order = strcmp(t->name, "lm_head.weight");
            if (head_name_order == 0) {
                if (t->rows != c->vocab_size || t->cols != d ||
                    (m->device == VI_DEVICE_CPU &&
                     memcmp(t->data, weights->embedding, c->vocab_size * d * sizeof(float)) != 0))
                    { int result = vi_model_problem(e, "tied LM head differs from embedding"); return result; }
                t->used = true;
            }
        }
    }
    for (size_t i = 0; i < c->num_layers; ++i) {
        vi_layer_weights *w = &weights->layers[i];
        /* Byte zero is reserved; the helper uses the next 192 bytes. */
        char name[193];
#define BIND(field, suffix, rows, cols) do { int bound = bind_layer_tensor(m, name, i, suffix, rows, cols, &w->field, &e); if (!bound) return 0; } while (0)
        BIND(input_norm, "input_layernorm.weight", d, 1);
        BIND(q, "self_attn.q_proj.weight", q, d);
        BIND(k, "self_attn.k_proj.weight", kv, d);
        BIND(v, "self_attn.v_proj.weight", kv, d);
        BIND(o, "self_attn.o_proj.weight", d, q);
        BIND(post_norm, "post_attention_layernorm.weight", d, 1);
        BIND(gate, "mlp.gate_proj.weight", f, d);
        BIND(up, "mlp.up_proj.weight", f, d);
        BIND(down, "mlp.down_proj.weight", d, f);
        if (c->qkv_bias) {
            BIND(q_bias, "self_attn.q_proj.bias", q, 1);
            BIND(k_bias, "self_attn.k_proj.bias", kv, 1);
            BIND(v_bias, "self_attn.v_proj.bias", kv, 1);
        }
        if (c->attention_output_bias) BIND(o_bias, "self_attn.o_proj.bias", d, 1);
#undef BIND
    }
    for (size_t i = 0; i < m->tensor_count; ++i)
        if (!m->tensors[i].used) { int result = vi_model_problem_string(e, "unrecognized/unused tensor: ", m->tensors[i].name); return result; }
    return 1;
}
static void free_weights(void *opaque)
{
    vi_llama_weights *weights = opaque;
    if (weights == NULL) return;
    free(weights->layers);
    free(weights);
}

static vi_status forward(void *opaque, const vi_model_input *input, float *logits, size_t vocab)
{
    vi_llama_state *s = opaque;
    if (s == NULL || input == NULL || input->tokens == NULL || logits == NULL || input->count == 0)
        return VI_INVALID;
    if (s->failed) return VI_MODEL_ERROR;
    const vi_llama_weights *model = s->model;
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

static void free_state(void *opaque)
{
    vi_llama_state *s = opaque;
    if (s == NULL) return;
    s->model->ops->destroy(s->context);
    s->model->ops->release(s->keys);
    s->model->ops->release(s->values);
    s->model->ops->release(s->workspace);
    free(s);
}
static int add_product(size_t *n, size_t a, size_t b)
{
    const size_t limit = SIZE_MAX / sizeof(float);
    if (a == 0 || b == 0 || a > limit / b || *n > limit - a * b) return 0;
    *n += a * b;
    return 1;
}

static void copy_state_error(char *error, size_t capacity, const char *message)
{
    size_t i = 0;
    while (i < capacity - 1 && message[i] != '\0') {
        error[i] = message[i];
        ++i;
    }
    error[i] = '\0';
}

static vi_status create_state(const vi_model *owner, size_t capacity,
                                void **out,
                                char *error, size_t error_capacity)
{
    const vi_llama_weights *model = owner->weights;
    const char *why = "invalid model or context capacity";
    vi_llama_state *s = NULL;
    if (model == NULL || out == NULL || capacity == 0 ||
        capacity > model->config.max_seq_len) goto fail;
    {
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
        *out = s;
        return VI_OK;
    }

fail:
    free_state(s);
    if (error != NULL && error_capacity != 0) copy_state_error(error, error_capacity, why);
    return VI_INVALID;
}

static size_t computed_tokens(const void *opaque)
{
    const vi_llama_state *state = opaque;
    return state->cached_tokens;
}

const vi_model_executor vi_llama_executor = {
    .configure = configure,
    .bind_weights = bind_weights,
    .free_weights = free_weights,
    .create_state = create_state,
    .free_state = free_state,
    .forward = forward,
    .computed_tokens = computed_tokens
};
