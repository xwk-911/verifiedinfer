#include "support/tiny_transformer.h"

#include <math.h>

static int config_valid(vi_tiny_transformer_config c)
{
    return vi_vocab_size_valid(c.vocab_size) && c.hidden_size != 0 &&
        c.intermediate_size != 0 && c.max_seq_len != 0 &&
        isfinite(c.rms_norm_epsilon) && c.rms_norm_epsilon > 0;
}

static int add_matrix(size_t *count, size_t rows, size_t cols)
{
    const size_t limit = SIZE_MAX / sizeof(float);
    if (rows == 0 || cols == 0 || rows > limit / cols ||
        *count > limit - rows * cols) {
        return 0;
    }
    *count += rows * cols;
    return 1;
}

size_t vi_tiny_transformer_weights_count(vi_tiny_transformer_config c)
{
    size_t n = 0;
    if (!config_valid(c) ||
        !add_matrix(&n, c.vocab_size, c.hidden_size) ||
        !add_matrix(&n, c.max_seq_len, c.hidden_size) ||
        !add_matrix(&n, 3, c.hidden_size)) {
        return 0;
    }
    for (size_t i = 0; i < 4; ++i) {
        if (!add_matrix(&n, c.hidden_size, c.hidden_size)) {
            return 0;
        }
    }
    for (size_t i = 0; i < 3; ++i) {
        if (!add_matrix(&n, c.intermediate_size, c.hidden_size)) {
            return 0;
        }
    }
    return add_matrix(&n, c.vocab_size, c.hidden_size) ? n : 0;
}

size_t vi_tiny_transformer_workspace_count(vi_tiny_transformer_config c)
{
    size_t n = 0;
    if (!config_valid(c) || !add_matrix(&n, 5, c.hidden_size) ||
        !add_matrix(&n, 2, c.intermediate_size) ||
        !add_matrix(&n, 1, c.max_seq_len)) {
        return 0;
    }
    return n;
}

size_t vi_tiny_transformer_kv_count(vi_tiny_transformer_config c)
{
    size_t n = 0;
    return config_valid(c) && add_matrix(&n, c.max_seq_len, c.hidden_size) ? n : 0;
}

vi_status vi_tiny_transformer_weights_init(vi_tiny_transformer_weights *weights, vi_tiny_transformer_config c,
                                const float *storage, size_t count)
{
    const size_t required = vi_tiny_transformer_weights_count(c);
    if (weights == NULL || storage == NULL || required == 0 || count < required ||
        count > SIZE_MAX / sizeof(float)) {
        return VI_INVALID;
    }
    for (size_t i = 0; i < required; ++i) {
        if (!isfinite(storage[i])) {
            return VI_INVALID;
        }
    }
    const size_t d = c.hidden_size, f = c.intermediate_size;
    vi_tiny_transformer_weights w = {.config = c};
    size_t offset = 0;
#define TAKE(field, size) do { w.field = storage + offset; offset += (size); } while (0)
    TAKE(token_embedding, c.vocab_size * d);
    TAKE(position_embedding, c.max_seq_len * d);
    TAKE(attention_norm, d);
    TAKE(q_proj, d * d);
    TAKE(k_proj, d * d);
    TAKE(v_proj, d * d);
    TAKE(o_proj, d * d);
    TAKE(ffn_norm, d);
    TAKE(gate_proj, f * d);
    TAKE(up_proj, f * d);
    TAKE(down_proj, d * f);
    TAKE(output_norm, d);
    TAKE(lm_head, c.vocab_size * d);
#undef TAKE
    *weights = w;
    return VI_OK;
}

static int finite_vector(const float *x, size_t n)
{
    for (size_t i = 0; i < n; ++i) {
        if (!isfinite(x[i])) {
            return 0;
        }
    }
    return 1;
}

static void linear(const float *weight, const float *x, float *out,
                   size_t rows, size_t cols)
{
    for (size_t i = 0; i < rows; ++i) {
        float sum = 0;
        for (size_t j = 0; j < cols; ++j) {
            sum += weight[i * cols + j] * x[j];
        }
        out[i] = sum;
    }
}

static int rms_norm(const float *x, const float *weight, float *out,
                    size_t n, float epsilon)
{
    float sum = 0;
    for (size_t i = 0; i < n; ++i) {
        sum += x[i] * x[i];
    }
    if (!isfinite(sum)) {
        return 0;
    }
    const float scale = 1.0f / sqrtf(sum / (float)n + epsilon);
    for (size_t i = 0; i < n; ++i) {
        out[i] = (x[i] * scale) * weight[i];
    }
    return finite_vector(out, n);
}

static vi_status tiny_transformer_forward(void *state, const vi_model_input *input,
                                float *logits, size_t vocab_size)
{
    vi_tiny_transformer_model *model = state;
    if (model == NULL || model->weights == NULL || input == NULL ||
        input->tokens == NULL || input->count == 0 || logits == NULL) {
        return VI_INVALID;
    }
    const vi_tiny_transformer_weights *w = model->weights;
    const vi_tiny_transformer_config c = w->config;
    const size_t needed = vi_tiny_transformer_workspace_count(c);
    if (vi_tiny_transformer_weights_count(c) == 0 || needed == 0 ||
        vocab_size != c.vocab_size || model->workspace == NULL ||
        model->workspace_count < needed ||
        model->workspace_count > SIZE_MAX / sizeof(float) ||
        model->cache.keys == NULL || model->cache.values == NULL ||
        model->cache.capacity != c.max_seq_len ||
        model->cache.len > model->cache.capacity || input->position != model->cache.len) {
        return VI_INVALID;
    }
    if (input->count > model->cache.capacity - model->cache.len) {
        return VI_NO_SPACE;
    }
    for (size_t i = 0; i < input->count; ++i) {
        if (input->tokens[i] >= vocab_size) {
            return VI_INVALID;
        }
    }
    const size_t d = c.hidden_size, f = c.intermediate_size;
    float *x = model->workspace;
    float *normed = x + d, *q = normed + d, *attention = q + d;
    float *projected = attention + d, *gate = projected + d;
    float *up = gate + f, *scores = up + f;
    const float attention_scale = 1.0f / sqrtf((float)d);

    for (size_t t = 0; t < input->count; ++t) {
        const size_t pos = input->position + t;
        float *key = model->cache.keys + pos * d;
        float *value = model->cache.values + pos * d;
        for (size_t j = 0; j < d; ++j) {
            x[j] = w->token_embedding[(size_t)input->tokens[t] * d + j] +
                w->position_embedding[pos * d + j];
        }
        if (!rms_norm(x, w->attention_norm, normed, d, c.rms_norm_epsilon)) {
            return VI_MODEL_ERROR;
        }
        linear(w->q_proj, normed, q, d, d);
        linear(w->k_proj, normed, key, d, d);
        linear(w->v_proj, normed, value, d, d);
        if (!finite_vector(q, d) || !finite_vector(key, d) || !finite_vector(value, d)) {
            return VI_MODEL_ERROR;
        }
        float maximum = -INFINITY;
        for (size_t k = 0; k <= pos; ++k) {
            float dot = 0;
            for (size_t j = 0; j < d; ++j) {
                dot += q[j] * model->cache.keys[k * d + j];
            }
            scores[k] = dot * attention_scale;
            if (scores[k] > maximum) {
                maximum = scores[k];
            }
        }
        if (!finite_vector(scores, pos + 1)) {
            return VI_MODEL_ERROR;
        }
        float total = 0;
        for (size_t k = 0; k <= pos; ++k) {
            scores[k] = expf(scores[k] - maximum);
            total += scores[k];
        }
        for (size_t j = 0; j < d; ++j) {
            float sum = 0;
            for (size_t k = 0; k <= pos; ++k) {
                sum += (scores[k] / total) * model->cache.values[k * d + j];
            }
            attention[j] = sum;
        }
        linear(w->o_proj, attention, projected, d, d);
        for (size_t j = 0; j < d; ++j) {
            x[j] += projected[j];
        }
        if (!rms_norm(x, w->ffn_norm, normed, d, c.rms_norm_epsilon)) {
            return VI_MODEL_ERROR;
        }
        linear(w->gate_proj, normed, gate, f, d);
        linear(w->up_proj, normed, up, f, d);
        for (size_t j = 0; j < f; ++j) {
            /* Stable SiLU avoids exp overflow for large negative inputs. */
            const float sigmoid = gate[j] >= 0
                ? 1.0f / (1.0f + expf(-gate[j]))
                : expf(gate[j]) / (1.0f + expf(gate[j]));
            gate[j] = (gate[j] * sigmoid) * up[j];
        }
        linear(w->down_proj, gate, projected, d, f);
        for (size_t j = 0; j < d; ++j) {
            x[j] += projected[j];
        }
        if (!finite_vector(x, d)) {
            return VI_MODEL_ERROR;
        }
    }
    if (!rms_norm(x, w->output_norm, normed, d, c.rms_norm_epsilon)) {
        return VI_MODEL_ERROR;
    }
    linear(w->lm_head, normed, logits, c.vocab_size, d);
    if (!finite_vector(logits, c.vocab_size)) {
        return VI_MODEL_ERROR;
    }
    model->cache.len += input->count;
    return VI_OK;
}

vi_status vi_tiny_transformer_model_init(vi_tiny_transformer_model *model, const vi_tiny_transformer_weights *weights,
                              float *keys, float *values, size_t kv_count,
                              float *workspace, size_t workspace_count,
                              vi_model_runner *runner)
{
    if (model == NULL || weights == NULL || runner == NULL ||
        keys == NULL || values == NULL || workspace == NULL) {
        return VI_INVALID;
    }
    const size_t kv_needed = vi_tiny_transformer_kv_count(weights->config);
    const size_t work_needed = vi_tiny_transformer_workspace_count(weights->config);
    if (vi_tiny_transformer_weights_count(weights->config) == 0 || kv_needed == 0 ||
        work_needed == 0 || kv_count < kv_needed || workspace_count < work_needed ||
        kv_count > SIZE_MAX / sizeof(float) || workspace_count > SIZE_MAX / sizeof(float)) {
        return VI_INVALID;
    }
    *model = (vi_tiny_transformer_model){.weights = weights,
        .cache = {.keys = keys, .values = values, .capacity = weights->config.max_seq_len},
        .workspace = workspace, .workspace_count = workspace_count};
    *runner = (vi_model_runner){.state = model, .forward = tiny_transformer_forward,
        .vocab_size = weights->config.vocab_size};
    return VI_OK;
}
