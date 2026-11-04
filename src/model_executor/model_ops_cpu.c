#include "model_internal.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

static vi_status create(void **context) { *context = NULL; return VI_OK; }
static void destroy(void *context) { (void)context; }
static float *allocate(void *context, size_t count)
{
    (void)context;
    return count <= SIZE_MAX / sizeof(float) ? malloc(count * sizeof(float)) : NULL;
}
static void release(float *data) { free(data); }
static vi_status copy(void *context, float *dst, const float *src, size_t count)
{
    (void)context;
    memcpy(dst, src, count * sizeof(float));
    return VI_OK;
}
static vi_status linear(void *context, const float *w, const float *bias,
                         const float *x, float *out, size_t rows, size_t cols)
{
    (void)context;
    for (size_t i = 0; i < rows; ++i) {
        float sum = 0;
        for (size_t j = 0; j < cols; ++j) sum += w[i * cols + j] * x[j];
        out[i] = bias == NULL ? sum : sum + bias[i];
    }
    return VI_OK;
}
static vi_status norm(void *context, const float *x, const float *w, float *out,
                       size_t n, float epsilon)
{
    (void)context;
    float squares = 0;
    for (size_t i = 0; i < n; ++i) squares += x[i] * x[i];
    if (!isfinite(squares)) return VI_MODEL_ERROR;
    float scale = 1.0f / sqrtf(squares / (float)n + epsilon);
    for (size_t i = 0; i < n; ++i) out[i] = (x[i] * scale) * w[i];
    return VI_OK;
}
static vi_status rope(void *context, float *x, size_t heads, size_t dim,
                       size_t position, float theta)
{
    (void)context;
    for (size_t h = 0; h < heads; ++h) {
        for (size_t i = 0; i < dim / 2; ++i) {
            float angle = (float)position * (1.0f / powf(theta, (float)(2 * i) / (float)dim));
            float c = cosf(angle), s = sinf(angle);
            size_t a = h * dim + i, b = a + dim / 2;
            float left = x[a], right = x[b];
            x[a] = left * c - right * s;
            x[b] = right * c + left * s;
        }
    }
    return VI_OK;
}
static vi_status attention(void *context, const float *q, const float *keys,
                            const float *values, float *out, float *scores,
                            size_t heads, size_t kv_heads, size_t dim,
                            size_t length, size_t capacity)
{
    (void)context;
    size_t kv_width = kv_heads * dim;
    float scale = 1.0f / sqrtf((float)dim);
    for (size_t h = 0; h < heads; ++h) {
        size_t kh = h / (heads / kv_heads);
        float *row = scores + h * capacity;
        float maximum = -INFINITY, total = 0;
        for (size_t t = 0; t < length; ++t) {
            float dot = 0;
            for (size_t j = 0; j < dim; ++j)
                dot += q[h * dim + j] * keys[t * kv_width + kh * dim + j];
            row[t] = dot * scale;
            if (row[t] > maximum) maximum = row[t];
        }
        for (size_t t = 0; t < length; ++t) {
            row[t] = expf(row[t] - maximum);
            total += row[t];
        }
        for (size_t j = 0; j < dim; ++j) {
            float sum = 0;
            for (size_t t = 0; t < length; ++t)
                sum += (row[t] / total) * values[t * kv_width + kh * dim + j];
            out[h * dim + j] = sum;
        }
    }
    return VI_OK;
}
static vi_status add(void *context, float *x, const float *y, size_t n)
{
    (void)context;
    for (size_t i = 0; i < n; ++i) x[i] += y[i];
    return VI_OK;
}
static vi_status swiglu(void *context, float *gate, const float *up, size_t n)
{
    (void)context;
    for (size_t i = 0; i < n; ++i) {
        float e = expf(gate[i] >= 0 ? -gate[i] : gate[i]);
        float sigmoid = gate[i] >= 0 ? 1.0f / (1.0f + e) : e / (1.0f + e);
        gate[i] = (gate[i] * sigmoid) * up[i];
    }
    return VI_OK;
}
const vi_model_ops *vi_cpu_model_ops(void)
{
    static const vi_model_ops ops = {create, destroy, allocate, release, copy, copy, copy,
                                    linear, norm, rope, attention, add, swiglu};
    return &ops;
}
