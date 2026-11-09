#include "verifiedinfer/engine/engine.h"
#include "request_internal.h"
#include "verifiedinfer/model_executor/sampler.h"

#include <string.h>

vi_status vi_engine_init(vi_engine *engine, vi_model_runner model_runner,
                         vi_token *history_storage, size_t history_capacity,
                         float *logits_workspace, size_t logits_capacity,
                         const vi_token *prompt, size_t prompt_len,
                         vi_request_config config)
{
    if (engine == NULL || model_runner.forward == NULL ||
        !vi_vocab_size_valid(model_runner.vocab_size) || logits_workspace == NULL ||
        logits_capacity < model_runner.vocab_size ||
        logits_capacity > SIZE_MAX / sizeof(float)) {
        return VI_INVALID;
    }
    vi_status status = vi_request_init_config(
        (vi_request *)engine, history_storage, history_capacity,
        prompt, prompt_len, model_runner.vocab_size, &config);
    if (status != VI_OK) {
        return status;
    }
    engine->model_runner = model_runner;
    engine->logits_workspace = logits_workspace;
    engine->logits_capacity = logits_capacity;
    return VI_OK;
}

static vi_status vi_engine_step_core(vi_engine *engine, vi_output *output,
                                     vi_sample_result *sample_view,
                                     vi_model_input *input_view)
{
    if (engine == NULL || output == NULL) {
        return VI_INVALID;
    }
    vi_request *request_state = (vi_request *)engine;
    vi_token_buffer *history_buffer = (vi_token_buffer *)request_state;
    vi_status status = vi_request_ready(request_state);
    if (status != VI_OK) {
        return status;
    }
    if (engine->model_runner.forward == NULL ||
        engine->model_runner.vocab_size != request_state->vocab_size ||
        engine->logits_workspace == NULL ||
        engine->logits_capacity < request_state->vocab_size ||
        engine->logits_capacity > SIZE_MAX / sizeof(float) ||
        output->logits == NULL || output->logits_capacity < request_state->vocab_size ||
        output->logits_capacity > SIZE_MAX / sizeof(float)) {
        return VI_INVALID;
    }

    const size_t vocab_size = engine->model_runner.vocab_size;
    input_view->tokens = history_buffer->data + request_state->kv_len;
    input_view->count = history_buffer->len - request_state->kv_len;
    input_view->position = request_state->kv_len;
    status = engine->model_runner.forward(
        engine->model_runner.state, input_view, engine->logits_workspace, vocab_size);
    if (status != VI_OK) {
        if (status == VI_MODEL_ERROR) request_state->phase = VI_FAILED;
        return VI_MODEL_ERROR;
    }
    status = vi_sample_greedy(engine->logits_workspace, vocab_size,
                              request_state->sampler_state, sample_view);
    if (status != VI_OK) {
        request_state->phase = VI_FAILED;
        return VI_MODEL_ERROR;
    }
    status = vi_request_commit(request_state, sample_view->token, sample_view->next_state);
    if (status != VI_OK) {
        /* A valid request and a footprint-respecting model_runner cannot fail here. */
        request_state->phase = VI_FAILED;
        return VI_MODEL_ERROR;
    }
    memcpy(output->logits, engine->logits_workspace, vocab_size * sizeof(float));
    output->vocab_size = vocab_size;
    output->token = sample_view->token;
    return VI_OK;
}

vi_status vi_engine_step(vi_engine *engine, vi_output *output)
{
    vi_sample_result sample;
    vi_model_input input;
    return vi_engine_step_core(engine, output, &sample, &input);
}
