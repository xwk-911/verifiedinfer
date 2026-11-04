#include "verifiedinfer/memory/token_buffer.h"

vi_status vi_token_buffer_init(vi_token_buffer *buffer, vi_token *storage,
                               size_t capacity)
{
    if (buffer == NULL || capacity > SIZE_MAX / sizeof(vi_token) ||
        (capacity != 0 && storage == NULL)) {
        return VI_INVALID;
    }
    buffer->data = storage;
    buffer->len = 0;
    buffer->capacity = capacity;
    return VI_OK;
}

vi_status vi_token_buffer_append(vi_token_buffer *buffer, vi_token token)
{
    if (buffer == NULL || buffer->len > buffer->capacity ||
        buffer->capacity > SIZE_MAX / sizeof(vi_token) ||
        (buffer->capacity != 0 && buffer->data == NULL)) {
        return VI_INVALID;
    }
    if (buffer->len == buffer->capacity) {
        return VI_NO_SPACE;
    }
    buffer->data[buffer->len] = token;
    buffer->len += 1;
    return VI_OK;
}
