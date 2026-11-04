#include <float.h>
#include <math.h>
#include <stdio.h>
#include <string.h>

#include "verifiedinfer/engine/engine.h"
#include "support/check.h"
#include "tiny_dense_weights.h"

/* Independent cold full-prefix reference: materialize all Q/K/V rows and the
 * causal score matrix before evaluating attention and the FFN. This does not
 * call the production forward or its helpers and never reuses a previous KV.
 * Same float operation order/libm, no FMA contraction: compare bytes, not epsilon. */
static void reference_norm(const float *x, const float *weight, size_t width,
                           float epsilon, float *out)
{
    float squares = 0;
    for (size_t j = 0; j < width; ++j) {
        squares += x[j] * x[j];
    }
    float inverse_rms = 1.0f / sqrtf(squares / (float)width + epsilon);
    for (size_t j = 0; j < width; ++j) {
        out[j] = (x[j] * inverse_rms) * weight[j];
    }
}

static void reference_projection(const float *matrix, size_t outputs, size_t inputs,
                                 const float *x, float *out)
{
    for (size_t row = 0; row < outputs; ++row) {
        out[row] = 0;
        for (size_t col = 0; col < inputs; ++col) {
            out[row] += matrix[row * inputs + col] * x[col];
        }
    }
}

static void reference_forward(const vi_dense_weights *w, const vi_token *tokens,
                              size_t n, float *logits, float *keys, float *values)
{
    CHECK(n > 0 && n <= TINY_CONTEXT);
    const size_t d = TINY_HIDDEN, f = TINY_FFN;
    CHECK(w->config.hidden_size == d && w->config.intermediate_size == f);
    float hidden[TINY_CONTEXT][TINY_HIDDEN], q[TINY_CONTEXT][TINY_HIDDEN];
    float scores[TINY_CONTEXT][TINY_CONTEXT];
    for (size_t row = 0; row < n; ++row) {
        float normalized[TINY_HIDDEN];
        for (size_t col = 0; col < d; ++col) {
            hidden[row][col] = w->token_embedding[(size_t)tokens[row] * d + col] +
                w->position_embedding[row * d + col];
        }
        reference_norm(hidden[row], w->attention_norm, d,
                       w->config.rms_norm_epsilon, normalized);
        reference_projection(w->q_proj, d, d, normalized, q[row]);
        reference_projection(w->k_proj, d, d, normalized, keys + row * d);
        reference_projection(w->v_proj, d, d, normalized, values + row * d);
    }
    const float scale = 1.0f / sqrtf((float)d);
    for (size_t row = 0; row < n; ++row) {
        for (size_t col = 0; col <= row; ++col) {
            float product = 0;
            for (size_t j = 0; j < d; ++j) {
                product += q[row][j] * keys[col * d + j];
            }
            scores[row][col] = product * scale;
        }
    }
    for (size_t row = 0; row < n; ++row) {
        float maximum = -INFINITY, denominator = 0;
        for (size_t col = 0; col <= row; ++col) {
            if (scores[row][col] > maximum) {
                maximum = scores[row][col];
            }
        }
        for (size_t col = 0; col <= row; ++col) {
            scores[row][col] = expf(scores[row][col] - maximum);
            denominator += scores[row][col];
        }
        float attended[TINY_HIDDEN], projected[TINY_HIDDEN], normalized[TINY_HIDDEN];
        for (size_t j = 0; j < d; ++j) {
            attended[j] = 0;
            for (size_t col = 0; col <= row; ++col) {
                attended[j] += (scores[row][col] / denominator) * values[col * d + j];
            }
        }
        reference_projection(w->o_proj, d, d, attended, projected);
        for (size_t j = 0; j < d; ++j) {
            hidden[row][j] += projected[j];
        }
        reference_norm(hidden[row], w->ffn_norm, d, w->config.rms_norm_epsilon, normalized);
        float gates[TINY_FFN], up[TINY_FFN];
        reference_projection(w->gate_proj, f, d, normalized, gates);
        reference_projection(w->up_proj, f, d, normalized, up);
        for (size_t j = 0; j < f; ++j) {
            float exponential = expf(gates[j] >= 0 ? -gates[j] : gates[j]);
            float sigmoid = gates[j] >= 0 ? 1.0f / (1.0f + exponential)
                                         : exponential / (1.0f + exponential);
            gates[j] = (gates[j] * sigmoid) * up[j];
        }
        reference_projection(w->down_proj, d, f, gates, projected);
        for (size_t j = 0; j < d; ++j) {
            hidden[row][j] += projected[j];
        }
    }
    float normalized[TINY_HIDDEN];
    reference_norm(hidden[n - 1], w->output_norm, d,
                   w->config.rms_norm_epsilon, normalized);
    reference_projection(w->lm_head, w->config.vocab_size, d, normalized, logits);
}

static void check_reference(const vi_dense_weights *weights, const vi_dense_model *model,
                            const vi_token *tokens, size_t count, const float *logits)
{
    float expected[TINY_VOCAB], keys[TINY_KV], values[TINY_KV];
    reference_forward(weights, tokens, count, expected, keys, values);
    CHECK(memcmp(expected, logits, sizeof(expected)) == 0);
    CHECK(model->cache.len == count);
    CHECK(memcmp(model->cache.keys, keys, count * TINY_HIDDEN * sizeof(float)) == 0);
    CHECK(memcmp(model->cache.values, values, count * TINY_HIDDEN * sizeof(float)) == 0);
}

static void test_all_chunk_partitions(void)
{
    float storage[TINY_WEIGHTS];
    vi_dense_weights weights;
    CHECK(tiny_dense_weights_init(&weights, storage) == VI_OK);
    const vi_token histories[][TINY_CONTEXT] = {
        {1, 2, 3, 39, 7, 0, 5, 8},
        {39, 39, 0, 1, 2, 39, 6, 4},
        {0, 0, 0, 0, 0, 0, 0, 0}
    };
    /* Each of the 2^(n-1) ways to partition the eight-token suffix stream. */
    for (size_t h = 0; h < sizeof(histories) / sizeof(histories[0]); ++h) {
        for (unsigned mask = 0; mask < (1u << (TINY_CONTEXT - 1)); ++mask) {
            float keys[TINY_KV], values[TINY_KV], workspace[TINY_WORKSPACE], logits[TINY_VOCAB];
            vi_dense_model model;
            vi_model_runner runner;
            CHECK(vi_dense_model_init(&model, &weights, keys, values, TINY_KV,
                                      workspace, TINY_WORKSPACE, &runner) == VI_OK);
            size_t start = 0;
            for (size_t end = 1; end <= TINY_CONTEXT; ++end) {
                if (end == TINY_CONTEXT || (mask & (1u << (end - 1)))) {
                    vi_model_input input = {.tokens = histories[h] + start,
                        .count = end - start, .position = start};
                    CHECK(runner.forward(runner.model, &input, logits, TINY_VOCAB) == VI_OK);
                    check_reference(&weights, &model, histories[h], end, logits);
                    start = end;
                }
            }
        }
    }
}

static void test_dense_engine_and_shared_weights(void)
{
    float storage[TINY_WEIGHTS], saved_weights[TINY_WEIGHTS];
    vi_dense_weights weights;
    CHECK(tiny_dense_weights_init(&weights, storage) == VI_OK);
    memcpy(saved_weights, storage, sizeof(storage));
    float keys[2][TINY_KV], values[2][TINY_KV], workspace[2][TINY_WORKSPACE];
    float scratch[2][TINY_VOCAB], logits[2][TINY_VOCAB];
    vi_token history[2][7];
    const vi_token prompts[2][3] = {{1, 2, 3}, {39, 0, 6}};
    vi_dense_model models[2];
    vi_model_runner runners[2];
    vi_engine engines[2];
    vi_output outputs[2] = {{.logits = logits[0], .logits_capacity = TINY_VOCAB},
                            {.logits = logits[1], .logits_capacity = TINY_VOCAB}};
    uint32_t states[2] = {7, 11};
    for (size_t r = 0; r < 2; ++r) {
        CHECK(vi_dense_model_init(&models[r], &weights, keys[r], values[r], TINY_KV,
                                  workspace[r], TINY_WORKSPACE, &runners[r]) == VI_OK);
        CHECK(vi_engine_init(&engines[r], runners[r], history[r], 7, scratch[r], TINY_VOCAB,
                             prompts[r], 3, (vi_request_config){.max_new_tokens = 4,
                             .initial_sampler_state = states[r]}) == VI_OK);
    }
    for (size_t step = 0; step < 4; ++step) {
        for (size_t r = 0; r < 2; ++r) {
            float expected[TINY_VOCAB], ref_keys[TINY_KV], ref_values[TINY_KV];
            reference_forward(&weights, history[r], 3 + step, expected, ref_keys, ref_values);
            /* Independent argmax, including this scaffold's state-dependent ties. */
            size_t chosen = states[r] % TINY_VOCAB;
            for (size_t i = 1; i < TINY_VOCAB; ++i) {
                size_t candidate = (states[r] % TINY_VOCAB + i) % TINY_VOCAB;
                if (expected[candidate] > expected[chosen]) {
                    chosen = candidate;
                }
            }
            CHECK(vi_engine_step(&engines[r], &outputs[r]) == VI_OK);
            CHECK(outputs[r].token == chosen);
            CHECK(memcmp(expected, logits[r], sizeof(expected)) == 0);
            check_reference(&weights, &models[r], history[r], 3 + step, logits[r]);
            states[r] = (uint32_t)(UINT64_C(1664525) * states[r] + UINT64_C(1013904223));
            CHECK(engines[r].request.sampler_state == states[r]);
            CHECK(engines[r].request.history.len == models[r].cache.len + 1);
        }
    }
    CHECK(memcmp(storage, saved_weights, sizeof(storage)) == 0);
    for (size_t r = 0; r < 2; ++r) {
        CHECK(engines[r].request.phase == VI_FINISHED);
        CHECK(vi_engine_step(&engines[r], &outputs[r]) == VI_DONE);
    }
    CHECK(memcmp(logits[0], logits[1], sizeof(logits[0])) != 0);
}

static void test_scalar_known_answer(void)
{
    /* Hand-computable model: one-dimensional Q=K=V=O=1, zero FFN.
     * For token 0, attention has one cell, so hidden = 1 + RMSNorm(1). */
    const vi_dense_config config = {.vocab_size = 2, .hidden_size = 1,
        .intermediate_size = 1, .max_seq_len = 2, .rms_norm_epsilon = 1};
    const float storage[] = {1, 2, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, -1};
    vi_dense_weights weights;
    CHECK(vi_dense_weights_count(config) == sizeof(storage) / sizeof(storage[0]));
    CHECK(vi_dense_weights_init(&weights, config, storage, 16) == VI_OK);
    float keys[2], values[2], workspace[9], logits[2];
    vi_dense_model model;
    vi_model_runner runner;
    CHECK(vi_dense_model_init(&model, &weights, keys, values, 2, workspace, 9, &runner) == VI_OK);
    const vi_token token = 0;
    vi_model_input input = {.tokens = &token, .count = 1};
    CHECK(runner.forward(runner.model, &input, logits, 2) == VI_OK);
    float kv = 1.0f / sqrtf(2.0f);
    float hidden = 1.0f + kv;
    float expected[] = {hidden * (1.0f / sqrtf(hidden * hidden + 1.0f)), 0};
    expected[1] = -expected[0];
    CHECK(keys[0] == kv && values[0] == kv);
    CHECK(memcmp(logits, expected, sizeof(expected)) == 0);
}

static void test_validation_and_failure_boundaries(void)
{
    float storage[TINY_WEIGHTS];
    vi_dense_weights weights;
    CHECK(tiny_dense_weights_init(&weights, storage) == VI_OK);
    CHECK(vi_dense_weights_count(weights.config) == TINY_WEIGHTS);
    CHECK(vi_dense_workspace_count(weights.config) == TINY_WORKSPACE);
    CHECK(vi_dense_kv_count(weights.config) == TINY_KV);
    vi_dense_config invalid = weights.config;
    invalid.hidden_size = SIZE_MAX;
    CHECK(vi_dense_weights_count(invalid) == 0);
    CHECK(vi_dense_workspace_count(invalid) == 0 && vi_dense_kv_count(invalid) == 0);
    invalid = weights.config;
    invalid.rms_norm_epsilon = NAN;
    CHECK(vi_dense_weights_count(invalid) == 0);
    vi_dense_weights untouched = {0};
    CHECK(vi_dense_weights_init(&untouched, weights.config, storage, TINY_WEIGHTS - 1) == VI_INVALID);
    CHECK(untouched.token_embedding == NULL);
    storage[0] = NAN;
    CHECK(vi_dense_weights_init(&untouched, weights.config, storage, TINY_WEIGHTS) == VI_INVALID);
    CHECK(tiny_dense_weights_init(&weights, storage) == VI_OK);
    float keys[TINY_KV], values[TINY_KV], workspace[TINY_WORKSPACE], logits[TINY_VOCAB];
    vi_dense_model model = {0};
    vi_model_runner runner = {0};
    CHECK(vi_dense_model_init(&model, &weights, keys, values, TINY_KV - 1,
                              workspace, TINY_WORKSPACE, &runner) == VI_INVALID);
    CHECK(model.weights == NULL && runner.forward == NULL);
    CHECK(vi_dense_model_init(&model, &weights, keys, values, TINY_KV,
                              workspace, TINY_WORKSPACE - 1, &runner) == VI_INVALID);
    CHECK(vi_dense_model_init(&model, &weights, keys, values, TINY_KV,
                              workspace, TINY_WORKSPACE, &runner) == VI_OK);
    const vi_token tokens[] = {1, 2, 3, 4, 5, 6, 7, 8};
    vi_model_input input = {.tokens = tokens, .count = 3, .position = 1};
    CHECK(runner.forward(runner.model, &input, logits, TINY_VOCAB) == VI_INVALID);
    CHECK(model.cache.len == 0);
    input.position = 0;
    const vi_token bad[] = {1, TINY_VOCAB};
    input.tokens = bad;
    input.count = 2;
    CHECK(runner.forward(runner.model, &input, logits, TINY_VOCAB) == VI_INVALID);
    CHECK(model.cache.len == 0);
    input.tokens = tokens;
    input.count = 3;
    CHECK(runner.forward(runner.model, &input, logits, TINY_VOCAB) == VI_OK);
    float saved_keys[3 * TINY_HIDDEN], saved_values[3 * TINY_HIDDEN];
    memcpy(saved_keys, keys, sizeof(saved_keys));
    memcpy(saved_values, values, sizeof(saved_values));
    input.position = 3;
    input.count = TINY_CONTEXT;
    CHECK(runner.forward(runner.model, &input, logits, TINY_VOCAB) == VI_NO_SPACE);
    CHECK(model.cache.len == 3 && memcmp(keys, saved_keys, sizeof(saved_keys)) == 0);
    CHECK(memcmp(values, saved_values, sizeof(saved_values)) == 0);

    /* A short output buffer must be rejected BEFORE consuming any model input. */
    vi_engine engine;
    vi_token history[7];
    float scratch[TINY_VOCAB];
    vi_output output = {.logits = logits, .logits_capacity = TINY_VOCAB - 1, .token = 99};
    CHECK(vi_dense_model_init(&model, &weights, keys, values, TINY_KV,
                              workspace, TINY_WORKSPACE, &runner) == VI_OK);
    CHECK(vi_engine_init(&engine, runner, history, 7, scratch, TINY_VOCAB - 1,
                         tokens, 3, (vi_request_config){.max_new_tokens = 4}) == VI_INVALID);
    CHECK(vi_engine_init(&engine, runner, history, 7, scratch, TINY_VOCAB,
                         tokens, 3, (vi_request_config){.max_new_tokens = 4}) == VI_OK);
    CHECK(vi_engine_step(&engine, &output) == VI_INVALID);
    CHECK(model.cache.len == 0 && engine.request.kv_len == 0 && output.token == 99);
    output.logits_capacity = TINY_VOCAB;
    CHECK(vi_engine_step(&engine, &output) == VI_OK);
    check_reference(&weights, &model, tokens, 3, logits);
}

static void test_numerical_failure_preserves_committed_prefix(void)
{
    float storage[TINY_WEIGHTS];
    vi_dense_weights weights;
    CHECK(tiny_dense_weights_init(&weights, storage) == VI_OK);
    /* Construct extreme but finite embeddings before any model borrows weights. */
    for (size_t j = 0; j < TINY_HIDDEN; ++j) {
        storage[39 * TINY_HIDDEN + j] = FLT_MAX;
    }
    float keys[TINY_KV], values[TINY_KV], workspace[TINY_WORKSPACE], logits[TINY_VOCAB];
    vi_dense_model model;
    vi_model_runner runner;
    CHECK(vi_dense_model_init(&model, &weights, keys, values, TINY_KV,
                              workspace, TINY_WORKSPACE, &runner) == VI_OK);
    const vi_token prefix[] = {1, 2};
    vi_model_input input = {.tokens = prefix, .count = 2};
    CHECK(runner.forward(runner.model, &input, logits, TINY_VOCAB) == VI_OK);
    float saved_keys[2 * TINY_HIDDEN], saved_values[2 * TINY_HIDDEN];
    memcpy(saved_keys, keys, sizeof(saved_keys));
    memcpy(saved_values, values, sizeof(saved_values));
    const vi_token suffix[] = {3, 39};
    input = (vi_model_input){.tokens = suffix, .count = 2, .position = 2};
    CHECK(runner.forward(runner.model, &input, logits, TINY_VOCAB) == VI_MODEL_ERROR);
    CHECK(model.cache.len == 2);
    CHECK(memcmp(keys, saved_keys, sizeof(saved_keys)) == 0);
    CHECK(memcmp(values, saved_values, sizeof(saved_values)) == 0);
    input.count = 1; /* Retry overwrites the uncommitted suffix. */
    CHECK(runner.forward(runner.model, &input, logits, TINY_VOCAB) == VI_OK);
    const vi_token accepted[] = {1, 2, 3};
    check_reference(&weights, &model, accepted, 3, logits);
}

int main(void)
{
    test_scalar_known_answer();
    test_all_chunk_partitions();
    test_dense_engine_and_shared_weights();
    test_validation_and_failure_boundaries();
    test_numerical_failure_preserves_committed_prefix();
    puts("PASS: dense exact cold-reference logits/KV, 384 chunk partitions, request isolation and failures");
    return 0;
}
