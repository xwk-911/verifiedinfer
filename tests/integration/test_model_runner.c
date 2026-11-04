#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "verifiedinfer/engine/engine.h"
#include "verifiedinfer/model_executor/model.h"
#include "verifiedinfer/model_executor/sampler.h"
#include "support/check.h"

int main(int argc, char **argv)
{
    CHECK(argc == 3);
    const vi_device device = strcmp(argv[2], "cuda") == 0 ? VI_DEVICE_CUDA : VI_DEVICE_CPU;
    char error[512];
    vi_model *model = NULL;
    CHECK(vi_model_load(argv[1], device, &model, error, sizeof(error)) == VI_OK);
    const vi_model_config *config = vi_model_get_config(model);
    CHECK(config->vocab_size > 4 && config->max_seq_len >= 8);
    const size_t v = config->vocab_size;
    float *full = malloc(v * sizeof(float)), *split = malloc(v * sizeof(float));
    float *logits[2] = {malloc(v * sizeof(float)), malloc(v * sizeof(float))};
    float *scratch[2] = {malloc(v * sizeof(float)), malloc(v * sizeof(float))};
    CHECK(full && split && logits[0] && logits[1] && scratch[0] && scratch[1]);
    vi_model_state *states[2] = {NULL, NULL};
    vi_model_runner runners[2];
    for (size_t i = 0; i < 2; ++i)
        CHECK(vi_model_state_create(model, 8, &states[i], &runners[i], error, sizeof(error)) == VI_OK);
    const vi_token tokens[] = {1, 2, 3, 4, 1};
    vi_model_input input = {.tokens = tokens, .count = 5};
    CHECK(runners[0].forward(runners[0].model, &input, full, v) == VI_OK);
    input.count = 2;
    CHECK(runners[1].forward(runners[1].model, &input, split, v) == VI_OK);
    CHECK(vi_model_cached_tokens(states[0]) == 5 && vi_model_cached_tokens(states[1]) == 2);
    input = (vi_model_input){.tokens = tokens + 2, .count = 3, .position = 2};
    CHECK(runners[1].forward(runners[1].model, &input, split, v) == VI_OK);
    CHECK(memcmp(full, split, v * sizeof(float)) == 0);
    input.position = 0;
    CHECK(runners[1].forward(runners[1].model, &input, split, v) == VI_INVALID);
    CHECK(vi_model_cached_tokens(states[1]) == 5);
    input.position = 5;
    input.count = 4;
    CHECK(runners[1].forward(runners[1].model, &input, split, v) == VI_NO_SPACE);
    CHECK(vi_model_cached_tokens(states[1]) == 5);
    const vi_token bad_token = (vi_token)v;
    input = (vi_model_input){.tokens = &bad_token, .count = 1, .position = 5};
    CHECK(runners[1].forward(runners[1].model, &input, split, v) == VI_INVALID);
    CHECK(vi_model_cached_tokens(states[1]) == 5);
    CHECK(memcmp(full, split, v * sizeof(float)) == 0);
    for (size_t i = 0; i < 2; ++i) {
        vi_model_state_free(states[i]); states[i] = NULL;
        CHECK(vi_model_state_create(model, 8, &states[i], &runners[i], error, sizeof(error)) == VI_OK);
    }
    vi_token histories[2][6];
    const vi_token prompts[2][3] = {{1, 2, 3}, {3, 2, 1}};
    vi_engine engines[2];
    vi_output outputs[2] = {{.logits = logits[0], .logits_capacity = v},
                            {.logits = logits[1], .logits_capacity = v}};
    for (size_t i = 0; i < 2; ++i)
        CHECK(vi_engine_init(&engines[i], runners[i], histories[i], 6, scratch[i], v, prompts[i], 3,
            (vi_request_config){.max_new_tokens = 3, .initial_sampler_state = (uint32_t)(7 + i)}) == VI_OK);
    for (size_t step = 0; step < 3; ++step) {
        for (size_t i = 0; i < 2; ++i) {
            vi_model_state *cold = NULL;
            vi_model_runner reference;
            CHECK(vi_model_state_create(model, 8, &cold, &reference, error, sizeof(error)) == VI_OK);
            input = (vi_model_input){.tokens = histories[i], .count = 3 + step};
            CHECK(reference.forward(reference.model, &input, full, v) == VI_OK);
            vi_sample_result expected;
            CHECK(vi_sample_greedy(full, v, engines[i].request.sampler_state, &expected) == VI_OK);
            CHECK(vi_engine_step(&engines[i], &outputs[i]) == VI_OK);
            CHECK(memcmp(full, logits[i], v * sizeof(float)) == 0);
            CHECK(outputs[i].token == expected.token);
            CHECK(engines[i].request.sampler_state == expected.next_state);
            CHECK(engines[i].request.history.len == vi_model_cached_tokens(states[i]) + 1);
            vi_model_state_free(cold);
        }
    }
    for (size_t i = 0; i < 2; ++i) {
        CHECK(vi_engine_step(&engines[i], &outputs[i]) == VI_DONE);
        vi_model_state_free(states[i]); free(logits[i]); free(scratch[i]);
    }
    vi_model_free(model); free(full); free(split);
    puts("PASS: compatible model exact cache continuation, shared-weight isolation, generation and preflight errors");
    return 0;
}
