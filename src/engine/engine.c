#include "verifiedinfer/engine/engine.h"
#include "verifiedinfer/model_executor/sampler.h"

#include <string.h>

vi_status vi_engine_init(vi_engine *engine, vi_model_runner model_runner,
                         vi_token *history_storage, size_t history_capacity,
                         float *logits_workspace, size_t logits_capacity,
                         const vi_token *prompt, size_t prompt_len,
                         vi_request_config config)
{
    vi_engine initial = {0};
    if (engine == NULL || model_runner.forward == NULL ||
        !vi_vocab_size_valid(model_runner.vocab_size) || logits_workspace == NULL ||
        logits_capacity < model_runner.vocab_size ||
        logits_capacity > SIZE_MAX / sizeof(float)) {
        return VI_INVALID;
    }
    vi_status status = vi_request_init(
        &initial.request, history_storage, history_capacity,
        prompt, prompt_len, model_runner.vocab_size, config);
    if (status != VI_OK) {
        return status;
    }
    initial.model_runner = model_runner;
    initial.logits_workspace = logits_workspace;
    initial.logits_capacity = logits_capacity;
    *engine = initial;
    return VI_OK;
}

vi_status vi_engine_step(vi_engine *engine, vi_output *output)
{
    vi_sample_result sample;
    if (engine == NULL || output == NULL) {
        return VI_INVALID;
    }
    vi_status status = vi_request_ready(&engine->request);
    if (status != VI_OK) {
        return status;
    }
    if (engine->model_runner.forward == NULL ||
        engine->model_runner.vocab_size != engine->request.vocab_size ||
        engine->logits_workspace == NULL ||
        engine->logits_capacity < engine->request.vocab_size ||
        engine->logits_capacity > SIZE_MAX / sizeof(float) ||
        output->logits == NULL || output->logits_capacity < engine->request.vocab_size ||
        output->logits_capacity > SIZE_MAX / sizeof(float)) {
        return VI_INVALID;
    }

    const size_t vocab_size = engine->model_runner.vocab_size;
    const vi_model_input input = {
        .tokens = engine->request.history.data + engine->request.kv_len,
        .count = engine->request.history.len - engine->request.kv_len,
        .position = engine->request.kv_len
    };
    status = engine->model_runner.forward(
        engine->model_runner.state, &input, engine->logits_workspace, vocab_size);
    if (status != VI_OK) {
        if (status == VI_MODEL_ERROR) engine->request.phase = VI_FAILED;
        return VI_MODEL_ERROR;
    }
    status = vi_sample_greedy(engine->logits_workspace, vocab_size,
                              engine->request.sampler_state, &sample);
    if (status != VI_OK) {
        engine->request.phase = VI_FAILED;
        return VI_MODEL_ERROR;
    }
    status = vi_request_commit(&engine->request, sample.token, sample.next_state);
    if (status != VI_OK) {
        /* A valid request and a footprint-respecting model_runner cannot fail here. */
        engine->request.phase = VI_FAILED;
        return VI_MODEL_ERROR;
    }
    memcpy(output->logits, engine->logits_workspace, vocab_size * sizeof(float));
    output->vocab_size = vocab_size;
    output->token = sample.token;
    return VI_OK;
}
