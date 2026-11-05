#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "verifiedinfer/engine/engine.h"
#include "support/tiny_transformer_weights.h"

#include "support/check.h"

static void test_prefill_decode_and_finish(void)
{
    vi_token history[7];
    const vi_token prompt[] = {1, 2, 3};
    float weights_storage[TINY_WEIGHTS], keys[TINY_KV], values[TINY_KV];
    float workspace[TINY_WORKSPACE], work[TINY_VOCAB], logits[TINY_VOCAB] = {0};
    vi_tiny_transformer_weights weights;
    vi_tiny_transformer_model model;
    vi_model_runner runner;
    vi_engine engine;
    vi_output output = {.logits = logits, .logits_capacity = TINY_VOCAB};
    CHECK(tiny_transformer_weights_init(&weights, weights_storage) == VI_OK);
    CHECK(vi_tiny_transformer_model_init(&model, &weights, keys, values, TINY_KV,
          workspace, TINY_WORKSPACE, &runner) == VI_OK);
    CHECK(vi_engine_init(&engine, runner, history, 7, work, TINY_VOCAB, prompt, 3,
                         (vi_request_config){.max_new_tokens = 4}) == VI_OK);
    CHECK(engine.request.phase == VI_PREFILL && engine.request.kv_len == 0);
    for (size_t i = 0; i < 4; ++i) {
        CHECK(vi_engine_step(&engine, &output) == VI_OK);
        CHECK(engine.request.history.len == 4 + i);
        CHECK(engine.request.kv_len == 3 + i && model.cache.len == engine.request.kv_len);
        CHECK(memcmp(history, prompt, sizeof(prompt)) == 0);
        CHECK(history[engine.request.history.len - 1] == output.token);
        CHECK(output.token < output.vocab_size && output.vocab_size == TINY_VOCAB);
        for (size_t j = 0; j < output.vocab_size; ++j)
            CHECK(output.logits[output.token] >= output.logits[j]);
    }
    CHECK(engine.request.phase == VI_FINISHED);
    const vi_output saved = output;
    float saved_logits[TINY_VOCAB];
    memcpy(saved_logits, logits, sizeof(logits));
    CHECK(vi_engine_step(&engine, &output) == VI_DONE);
    CHECK(model.cache.len == 6 && engine.request.history.len == 7);
    CHECK(output.token == saved.token);
    CHECK(memcmp(output.logits, saved_logits, sizeof(saved_logits)) == 0);
}

static void test_independent_requests(void)
{
    vi_token histories[2][5];
    const vi_token prompt[] = {1, 2};
    float weights_storage[TINY_WEIGHTS];
    vi_tiny_transformer_weights weights;
    CHECK(tiny_transformer_weights_init(&weights, weights_storage) == VI_OK);
    vi_tiny_transformer_model models[2];
    vi_model_runner runners[2];
    vi_engine engines[2];
    float keys[2][TINY_KV], values[2][TINY_KV], workspace[2][TINY_WORKSPACE];
    float work[2][TINY_VOCAB], logits[2][TINY_VOCAB];
    vi_output outputs[2] = {
        {.logits = logits[0], .logits_capacity = TINY_VOCAB},
        {.logits = logits[1], .logits_capacity = TINY_VOCAB}
    };
    for (size_t i = 0; i < 2; ++i) {
        CHECK(vi_tiny_transformer_model_init(&models[i], &weights, keys[i], values[i], TINY_KV,
              workspace[i], TINY_WORKSPACE, &runners[i]) == VI_OK);
        CHECK(vi_engine_init(&engines[i], runners[i], histories[i], 5, work[i], TINY_VOCAB,
              prompt, 2, (vi_request_config){.max_new_tokens = 3,
              .initial_sampler_state = 19}) == VI_OK);
    }
    for (size_t step = 0; step < 3; ++step) {
        CHECK(vi_engine_step(&engines[1], &outputs[1]) == VI_OK);
        CHECK(models[0].cache.len == (step ? step + 1 : 0));
        CHECK(vi_engine_step(&engines[0], &outputs[0]) == VI_OK);
        CHECK(outputs[0].token == outputs[1].token);
        CHECK(memcmp(outputs[0].logits, outputs[1].logits, sizeof(logits[0])) == 0);
        CHECK(engines[0].request.sampler_state == engines[1].request.sampler_state);
        CHECK(memcmp(keys[0], keys[1], models[0].cache.len * TINY_HIDDEN * sizeof(float)) == 0);
    }
}

static vi_status equal_logits(void *model, const vi_model_input *input,
                               float *logits, size_t vocab_size)
{
    (void)model;
    CHECK(input->count > 0);
    for (size_t i = 0; i < vocab_size; ++i) {
        logits[i] = 0;
    }
    return VI_OK;
}

static void test_eos_and_sampling_state(void)
{
    vi_token history[4];
    const vi_token prompt[] = {1};
    vi_model_runner model_runner = {.forward = equal_logits, .vocab_size = 8};
    vi_engine engine;
    float work[8], logits[8] = {0};
    vi_output output = {.logits = logits, .logits_capacity = 8};
    vi_request_config config = {.max_new_tokens = 3, .initial_sampler_state = 2,
                                .stop_on_eos = true, .eos_token = 2};
    CHECK(vi_engine_init(&engine, model_runner, history, 4, work, 8, prompt, 1, config) == VI_OK);
    CHECK(vi_engine_step(&engine, &output) == VI_OK && output.token == 2);
    CHECK(engine.request.phase == VI_FINISHED && engine.request.kv_len == 1);
    CHECK(engine.request.sampler_state != config.initial_sampler_state);
    config.stop_on_eos = false;
    CHECK(vi_engine_init(&engine, model_runner, history, 4, work, 8, prompt, 1, config) == VI_OK);
    CHECK(vi_engine_step(&engine, &output) == VI_OK && engine.request.phase == VI_DECODE);
    config.max_new_tokens = 0;
    CHECK(vi_engine_init(&engine, model_runner, history, 4, work, 8, prompt, 1, config) == VI_OK);
    CHECK(vi_engine_step(&engine, &output) == VI_DONE);
}

static vi_status reject_capacity(void *state, const vi_model_input *input,
                                  float *logits, size_t vocab_size)
{
    (void)state; (void)input; (void)logits; (void)vocab_size;
    return VI_NO_SPACE;
}

static void test_initialization_and_model_failure(void)
{
    vi_token history[] = {91, 92, 93};
    const vi_token prompt[] = {1, 2};
    vi_model_runner runner = {.forward = reject_capacity, .vocab_size = 8};
    vi_engine engine = {0};
    float work[8], logits[8] = {0};
    vi_output output = {.logits = logits, .logits_capacity = 8, .token = 99};
    CHECK(vi_engine_init(&engine, runner, history, 3, work, 8, prompt, 2,
                         (vi_request_config){.max_new_tokens = SIZE_MAX}) == VI_INVALID);
    CHECK(history[0] == 91 && engine.request.history.data == NULL);
    CHECK(vi_engine_init(&engine, runner, history, 3, work, 8, prompt, 2,
                         (vi_request_config){.max_new_tokens = 1}) == VI_OK);
    CHECK(vi_engine_step(&engine, &output) == VI_MODEL_ERROR);
    CHECK(engine.request.phase == VI_PREFILL && engine.request.kv_len == 0 && engine.request.history.len == 2);
    CHECK(output.token == 99 && logits[0] == 0);
    const vi_token invalid_prompt[] = {8};
    CHECK(vi_engine_init(&engine, runner, history, 3, work, 8, invalid_prompt, 1,
                         (vi_request_config){.max_new_tokens = 1}) == VI_INVALID);
    CHECK(history[0] == 1 && history[1] == 2);
}

static vi_status invalid_logits(void *model, const vi_model_input *input,
                                 float *logits, size_t vocab_size)
{
    (void)model;
    (void)input;
    for (size_t i = 0; i < vocab_size; ++i) {
        logits[i] = NAN;
    }
    return VI_OK;
}

static void test_model_contract_violation(void)
{
    vi_token history[2];
    const vi_token prompt[] = {1};
    vi_model_runner model_runner = {.forward = invalid_logits, .vocab_size = 8};
    vi_engine engine;
    float work[8], logits[8] = {0};
    vi_output output = {.logits = logits, .logits_capacity = 8, .token = 99};
    CHECK(vi_engine_init(&engine, model_runner, history, 2, work, 8, prompt, 1,
                         (vi_request_config){.max_new_tokens = 1}) == VI_OK);
    CHECK(vi_engine_step(&engine, &output) == VI_MODEL_ERROR);
    CHECK(logits[0] == 0);
    CHECK(engine.request.phase == VI_FAILED && engine.request.history.len == 1 && output.token == 99);
    CHECK(vi_engine_step(&engine, &output) == VI_MODEL_ERROR);
}

static vi_status fatal_model_error(void *model, const vi_model_input *input,
                                    float *logits, size_t vocab_size)
{
    (void)input;
    (void)vocab_size;
    size_t *calls = model;
    ++*calls;
    logits[0] = 123; /* Scratch may change, published output must not. */
    return VI_MODEL_ERROR;
}

static void test_fatal_model_error_is_terminal(void)
{
    size_t calls = 0;
    vi_model_runner runner = {.state = &calls, .forward = fatal_model_error, .vocab_size = 8};
    vi_token history[2];
    const vi_token prompt[] = {1};
    float work[8], logits[8] = {42};
    vi_engine engine;
    vi_output output = {.logits = logits, .logits_capacity = 8, .token = 99};
    CHECK(vi_engine_init(&engine, runner, history, 2, work, 8, prompt, 1,
                        (vi_request_config){.max_new_tokens = 1}) == VI_OK);
    CHECK(vi_engine_step(&engine, &output) == VI_MODEL_ERROR);
    CHECK(engine.request.phase == VI_FAILED && engine.request.kv_len == 0);
    CHECK(logits[0] == 42 && output.token == 99);
    CHECK(vi_engine_step(&engine, &output) == VI_MODEL_ERROR && calls == 1);
}

int main(void)
{
    test_prefill_decode_and_finish();
    test_independent_requests();
    test_eos_and_sampling_state();
    test_initialization_and_model_failure();
    test_model_contract_violation();
    test_fatal_model_error_is_terminal();
    puts("PASS: request lifecycle, KV prefix, sampling and failures");
    return 0;
}
