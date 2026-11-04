#include "verifiedinfer/engine/request.h"

#include <string.h>

static int stopping_policy_valid(vi_request_config config, size_t vocab_size)
{
    if ((config.stop_on_eos && config.eos_token >= vocab_size) ||
        config.stop_token_count > SIZE_MAX / sizeof(vi_token) ||
        (config.stop_token_count != 0 && config.stop_token_ids == NULL)) return 0;
    for (size_t i = 0; i < config.stop_token_count; ++i)
        if (config.stop_token_ids[i] >= vocab_size) return 0;
    return 1;
}

static int is_stop_token(vi_request_config config, vi_token token)
{
    if (config.stop_on_eos && token == config.eos_token) return 1;
    for (size_t i = 0; i < config.stop_token_count; ++i)
        if (token == config.stop_token_ids[i]) return 1;
    return 0;
}

vi_status vi_request_init(vi_request *request, vi_token *history_storage,
                          size_t history_capacity, const vi_token *prompt,
                          size_t prompt_len, size_t vocab_size,
                          vi_request_config config)
{
    vi_request initial = {0};
    if (request == NULL || prompt == NULL || prompt_len == 0 ||
        !vi_vocab_size_valid(vocab_size) ||
        prompt_len > history_capacity ||
        config.max_new_tokens > history_capacity - prompt_len ||
        !stopping_policy_valid(config, vocab_size)) {
        return VI_INVALID;
    }
    if (vi_token_buffer_init(&initial.history, history_storage,
                              history_capacity) != VI_OK) {
        return VI_INVALID;
    }
    for (size_t i = 0; i < prompt_len; ++i) {
        if (prompt[i] >= vocab_size) {
            return VI_INVALID;
        }
    }
    memmove(history_storage, prompt, prompt_len * sizeof(vi_token));
    initial.history.len = prompt_len;
    initial.prompt_len = prompt_len;
    initial.vocab_size = vocab_size;
    initial.sampler_state = config.initial_sampler_state;
    initial.config = config;
    initial.phase = config.max_new_tokens == 0 ? VI_FINISHED : VI_PREFILL;
    *request = initial;
    return VI_OK;
}

vi_status vi_request_ready(const vi_request *request)
{
    if (request == NULL) {
        return VI_INVALID;
    }
    if (request->phase == VI_FINISHED) {
        return VI_DONE;
    }
    if (request->phase == VI_FAILED) {
        return VI_MODEL_ERROR;
    }
    if ((request->phase != VI_PREFILL && request->phase != VI_DECODE) ||
        !vi_vocab_size_valid(request->vocab_size) ||
        request->history.data == NULL || request->prompt_len == 0 ||
        request->history.len < request->prompt_len ||
        request->history.capacity > SIZE_MAX / sizeof(vi_token) ||
        request->history.len >= request->history.capacity ||
        request->history.len - request->prompt_len >= request->config.max_new_tokens ||
        !stopping_policy_valid(request->config, request->vocab_size) ||
        (request->phase == VI_PREFILL &&
         (request->kv_len != 0 || request->history.len != request->prompt_len)) ||
        (request->phase == VI_DECODE && request->kv_len != request->history.len - 1)) {
        return VI_INVALID;
    }
    return VI_OK;
}

vi_status vi_request_commit(vi_request *request, vi_token token,
                            uint32_t next_sampler_state)
{
    vi_status status = vi_request_ready(request);
    if (status != VI_OK) {
        return status;
    }
    if (token >= request->vocab_size) {
        return VI_INVALID;
    }
    const size_t processed_len = request->history.len;
    status = vi_token_buffer_append(&request->history, token);
    if (status != VI_OK) {
        return status;
    }
    request->kv_len = processed_len;
    request->sampler_state = next_sampler_state;
    request->phase =
        request->history.len - request->prompt_len == request->config.max_new_tokens ||
        is_stop_token(request->config, token)
        ? VI_FINISHED : VI_DECODE;
    return VI_OK;
}
