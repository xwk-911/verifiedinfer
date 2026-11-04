#include "verifiedinfer/model_executor/models/mock_model.h"

static vi_status mock_forward(void *model, const vi_model_input *input,
                               float *logits, size_t vocab_size)
{
    vi_mock_model *mock = model;
    if (mock == NULL || input == NULL || input->tokens == NULL ||
        logits == NULL || input->count == 0 || !vi_vocab_size_valid(vocab_size) ||
        input->position != mock->cache.len ||
        mock->cache.len > mock->cache.capacity ||
        mock->cache.capacity > SIZE_MAX / sizeof(vi_token) ||
        (mock->cache.capacity != 0 && mock->cache.data == NULL) ||
        mock->forward_calls == SIZE_MAX || mock->prefix_hash >= 251u) {
        return VI_INVALID;
    }
    const vi_token *tokens = input->tokens;
    const size_t count = input->count;
    if (count > mock->cache.capacity - mock->cache.len) {
        return VI_NO_SPACE;
    }
    for (size_t i = 0; i < count; ++i) {
        if (tokens[i] >= vocab_size) {
            return VI_INVALID;
        }
    }
    for (size_t i = 0; i < count; ++i) {
        mock->prefix_hash = (uint32_t)(((uint64_t)mock->prefix_hash * 17u +
                                       tokens[i] + 1u) % 251u);
        mock->cache.data[mock->cache.len++] = tokens[i];
    }
    for (size_t i = 0; i < vocab_size; ++i) {
        logits[i] = (float)(((uint64_t)mock->prefix_hash + (uint64_t)i * 17u) % 11u);
    }
    mock->forward_calls += 1;
    return VI_OK;
}

vi_status vi_mock_model_init(vi_mock_model *mock, vi_token *cache_storage,
                               size_t capacity, size_t vocab_size,
                               vi_model_runner *model_runner)
{
    vi_mock_model initial = {0};
    if (mock == NULL || model_runner == NULL || !vi_vocab_size_valid(vocab_size) ||
        vi_token_buffer_init(&initial.cache, cache_storage, capacity) != VI_OK) {
        return VI_INVALID;
    }
    *mock = initial;
    *model_runner = (vi_model_runner){.model = mock, .forward = mock_forward,
                            .vocab_size = vocab_size};
    return VI_OK;
}
