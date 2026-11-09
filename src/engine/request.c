#include "verifiedinfer/engine/request.h"
#include "request_internal.h"

#include <string.h>

static int stopping_policy_valid(const vi_request_config *config, size_t vocab_size)
{
    if ((config->stop_on_eos && config->eos_token >= vocab_size) ||
        config->stop_token_count > SIZE_MAX / sizeof(vi_token) ||
        (config->stop_token_count != 0 && config->stop_token_ids == NULL)) return 0;
    for (size_t i = 0; i < config->stop_token_count; ++i)
        if (config->stop_token_ids[i] >= vocab_size) return 0;
    return 1;
}

static int is_stop_token(const vi_request_config *config, vi_token token)
{
    if (config->stop_on_eos && token == config->eos_token) return 1;
    for (size_t i = 0; i < config->stop_token_count; ++i)
        if (token == config->stop_token_ids[i]) return 1;
    return 0;
}

vi_status vi_request_init_config(vi_request *request, vi_token *history_storage,
                          size_t history_capacity, const vi_token *prompt,
                          size_t prompt_len, size_t vocab_size,
                          const vi_request_config *config)
{
    if (request == NULL || prompt == NULL || prompt_len == 0 ||
        !vi_vocab_size_valid(vocab_size) ||
        prompt_len > history_capacity ||
        config->max_new_tokens > history_capacity - prompt_len ||
        !stopping_policy_valid(config, vocab_size)) {
        return VI_INVALID;
    }
    if (history_capacity > SIZE_MAX / sizeof(vi_token) ||
        (history_capacity != 0 && history_storage == NULL)) {
        return VI_INVALID;
    }
    for (size_t i = 0; i < prompt_len; ++i) {
        if (prompt[i] >= vocab_size) {
            return VI_INVALID;
        }
    }
    memmove(history_storage, prompt, prompt_len * sizeof(vi_token));
    const size_t snapshot_budget = config->max_new_tokens;
    const uint32_t snapshot_sampler = config->initial_sampler_state;
    /* Publish the borrowed config before writing the remaining descriptor.
     * Its fields are read-only for this call; prompt/history and the request
     * descriptor are disjoint. All failure paths have already returned. */
    request->config = *config;
    vi_token_buffer *history_buffer = (vi_token_buffer *)request;
    history_buffer->data = history_storage;
    history_buffer->len = prompt_len;
    history_buffer->capacity = history_capacity;
    request->prompt_len = prompt_len;
    request->kv_len = 0;
    request->vocab_size = vocab_size;
    request->sampler_state = snapshot_sampler;
    request->phase = snapshot_budget == 0 ? VI_FINISHED : VI_PREFILL;
    return VI_OK;
}

vi_status vi_request_init(vi_request *request, vi_token *history_storage,
                          size_t history_capacity, const vi_token *prompt,
                          size_t prompt_len, size_t vocab_size,
                          vi_request_config config)
{
    return vi_request_init_config(request, history_storage, history_capacity,
                                  prompt, prompt_len, vocab_size, &config);
}

vi_status vi_request_ready(const vi_request *request)
{
    if (request == NULL) {
        return VI_INVALID;
    }
    const vi_token_buffer *history_buffer = (const vi_token_buffer *)request;
    if (request->phase == VI_FINISHED) {
        return VI_DONE;
    }
    if (request->phase == VI_FAILED) {
        return VI_MODEL_ERROR;
    }
    if ((request->phase != VI_PREFILL && request->phase != VI_DECODE) ||
        !vi_vocab_size_valid(request->vocab_size) ||
        history_buffer->data == NULL || request->prompt_len == 0 ||
        history_buffer->len < request->prompt_len ||
        history_buffer->capacity > SIZE_MAX / sizeof(vi_token) ||
        history_buffer->len >= history_buffer->capacity ||
        history_buffer->len - request->prompt_len >= request->config.max_new_tokens ||
        !stopping_policy_valid(&request->config, request->vocab_size) ||
        (request->phase == VI_PREFILL &&
         (request->kv_len != 0 || history_buffer->len != request->prompt_len)) ||
        (request->phase == VI_DECODE && request->kv_len != history_buffer->len - 1)) {
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
    vi_token_buffer *history_buffer = (vi_token_buffer *)request;
    const size_t processed_len = history_buffer->len;
    status = vi_token_buffer_append(history_buffer, token);
    if (status != VI_OK) {
        return status;
    }
    request->kv_len = processed_len;
    request->sampler_state = next_sampler_state;
    request->phase =
        history_buffer->len - request->prompt_len == request->config.max_new_tokens ||
        is_stop_token(&request->config, token)
        ? VI_FINISHED : VI_DECODE;
    return VI_OK;
}
