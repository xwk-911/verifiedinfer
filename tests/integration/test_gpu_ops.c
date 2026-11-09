#include "../../src/model_executor/model_internal.h"
#include "support/check.h"

#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const vi_model_ops *vi_reference_cuda_model_ops(void);

enum { BUFFER_COUNT = 6, GUARD = 4 };
struct fixture {
    const vi_model_ops *ops;
    void *context;
    float *buffers[BUFFER_COUNT];
    size_t lengths[BUFFER_COUNT];
};

static void initialize(struct fixture *f, const vi_model_ops *ops)
{
    memset(f, 0, sizeof(*f));
    f->ops = ops;
    CHECK(ops->create(&f->context) == VI_OK);
}

static float *buffer(struct fixture *f, unsigned slot, size_t n, unsigned seed)
{
    CHECK(slot < BUFFER_COUNT && !f->buffers[slot]);
    float *host = malloc((n + 2 * GUARD) * sizeof(float));
    CHECK(host);
    for (size_t i = 0; i < n + 2 * GUARD; ++i)
        host[i] = i < GUARD ? -9876.25f : i >= n + GUARD ? 12345.5f :
                  (float)((int)((i * 17 + seed * 13) % 101) - 50) / 32.0f;
    f->lengths[slot] = n;
    f->buffers[slot] = f->ops->allocate(f->context, n + 2 * GUARD);
    CHECK(f->buffers[slot]);
    CHECK(f->ops->write(f->context, f->buffers[slot], host, n + 2 * GUARD) == VI_OK);
    free(host);
    return f->buffers[slot] + GUARD;
}

static void compare_and_clear(struct fixture f[2], const char *label)
{
    for (unsigned slot = 0; slot < BUFFER_COUNT; ++slot) {
        if (!f[0].buffers[slot]) continue;
        CHECK(f[1].buffers[slot] && f[0].lengths[slot] == f[1].lengths[slot]);
        size_t n = f[0].lengths[slot], bytes = (n + 2 * GUARD) * sizeof(float);
        float *actual[2] = {malloc(bytes), malloc(bytes)};
        CHECK(actual[0] && actual[1]);
        for (unsigned k = 0; k < 2; ++k)
            CHECK(f[k].ops->read(f[k].context, actual[k], f[k].buffers[slot],
                                n + 2 * GUARD) == VI_OK);
        if (memcmp(actual[0], actual[1], bytes) != 0) {
            fprintf(stderr, "%s slot %u differs from the original CUDA plan\n", label, slot);
            abort();
        }
        for (unsigned i = 0; i < GUARD; ++i) {
            CHECK(actual[1][i] == -9876.25f);
            CHECK(actual[1][n + GUARD + i] == 12345.5f);
        }
        for (unsigned k = 0; k < 2; ++k) {
            free(actual[k]);
            f[k].ops->release(f[k].buffers[slot]);
            f[k].buffers[slot] = NULL;
        }
    }
}

static void elementwise(struct fixture f[2], size_t n, unsigned kind)
{
    for (unsigned k = 0; k < 2; ++k) {
        float *x = buffer(&f[k], 0, n, 1), *y = buffer(&f[k], 1, n, 2);
        if (kind == 0) CHECK(f[k].ops->add(f[k].context, x, y, n) == VI_OK);
        else if (kind == 1) CHECK(f[k].ops->swiglu(f[k].context, x, y, n) == VI_OK);
        else if (kind == 2) CHECK(f[k].ops->add(f[k].context, x, x, n) == VI_OK);
        else {
            float *out = buffer(&f[k], 2, n, 3);
            CHECK(f[k].ops->norm(f[k].context, x, y, out, n, 1e-5f) == VI_OK);
        }
    }
    compare_and_clear(f, "elementwise/norm");
}

static void rope_case(struct fixture f[2], size_t heads, size_t dim, size_t pos)
{
    for (unsigned k = 0; k < 2; ++k) {
        float *x = buffer(&f[k], 0, heads * dim, 4);
        CHECK(f[k].ops->rope(f[k].context, x, heads, dim, pos, 10000.f) == VI_OK);
    }
    compare_and_clear(f, "RoPE");
}

static void attention_case(struct fixture f[2], size_t heads, size_t kv_heads,
                           size_t dim, size_t length)
{
    size_t capacity = length + 3;
    for (unsigned k = 0; k < 2; ++k) {
        float *q = buffer(&f[k], 0, heads * dim, 1);
        float *keys = buffer(&f[k], 1, capacity * kv_heads * dim, 2);
        float *values = buffer(&f[k], 2, capacity * kv_heads * dim, 3);
        float *out = buffer(&f[k], 3, heads * dim, 4);
        float *scores = buffer(&f[k], 4, heads * capacity, 5);
        CHECK(f[k].ops->attention(f[k].context, q, keys, values, out, scores,
                                  heads, kv_heads, dim, length, capacity) == VI_OK);
    }
    compare_and_clear(f, "attention");
}

static void linear_case(struct fixture f[2], size_t rows, size_t cols, bool bias)
{
    for (unsigned k = 0; k < 2; ++k) {
        float *w = buffer(&f[k], 0, rows * cols, 1);
        float *x = buffer(&f[k], 1, cols, 2);
        float *out = buffer(&f[k], 2, rows, 3);
        float *b = bias ? buffer(&f[k], 3, rows, 4) : NULL;
        CHECK(f[k].ops->linear(f[k].context, w, b, x, out, rows, cols) == VI_OK);
    }
    compare_and_clear(f, "cuBLAS/PTX bias");
}

int main(void)
{
    struct fixture f[2];
    initialize(&f[0], vi_reference_cuda_model_ops());
    initialize(&f[1], vi_cuda_model_ops());
    unsigned cases = 0;
    const size_t lengths[] = {1, 31, 32, 255, 256, 257, 769};
    for (unsigned i = 0; i < sizeof(lengths) / sizeof(lengths[0]); ++i)
        for (unsigned kind = 0; kind < 4; ++kind) {
            elementwise(f, lengths[i], kind);
            ++cases;
        }
    const size_t positions[] = {0, 1, 37, 2048};
    for (unsigned i = 0; i < sizeof(positions) / sizeof(positions[0]); ++i)
        for (size_t dim = 2; dim <= 32; dim *= 4) {
            rope_case(f, 3, dim, positions[i]);
            ++cases;
        }
    for (size_t length = 1; length <= 7; length += 3)
        for (size_t kv_heads = 1; kv_heads <= 4; kv_heads *= 2) {
            attention_case(f, 4, kv_heads, 8, length);
            ++cases;
        }
    attention_case(f, 33, 1, 8, 2); ++cases;
    for (unsigned i = 0; i < 3; ++i)
        for (unsigned bias = 0; bias < 2; ++bias) {
            linear_case(f, lengths[i + 2], lengths[i], bias != 0);
            ++cases;
        }
    const vi_model_ops *ops = f[1].ops;
    void *c = f[1].context;
    CHECK(ops->add(c, NULL, NULL, 0) == VI_OK);
    CHECK(ops->swiglu(c, NULL, NULL, 0) == VI_OK);
    CHECK(ops->copy(c, NULL, NULL, 0) == VI_OK);
    CHECK(ops->allocate(c, SIZE_MAX) == NULL);
    CHECK(ops->copy(c, NULL, NULL, SIZE_MAX) == VI_INVALID);
    CHECK(ops->add(c, NULL, NULL, SIZE_MAX) == VI_INVALID);
    CHECK(ops->norm(c, NULL, NULL, NULL, 0, 1e-5f) == VI_INVALID);
    CHECK(ops->rope(c, NULL, 1, 3, 0, 10000.f) == VI_INVALID);
    CHECK(ops->linear(c, NULL, NULL, NULL, NULL, (size_t)INT_MAX + 1, 1) == VI_INVALID);
    CHECK(ops->attention(c, NULL, NULL, NULL, NULL, NULL, 4, 3, 8, 1, 1) == VI_INVALID);
    for (unsigned k = 0; k < 2; ++k) f[k].ops->destroy(f[k].context);
    printf("PASS: %u exact CUDA/PTX operator comparisons, guards, aliasing, cuBLAS composition and invalid sizes\n", cases);
    return 0;
}
