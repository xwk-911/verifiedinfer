#ifndef VI_TOKEN_BUFFER_H
#define VI_TOKEN_BUFFER_H

#include "verifiedinfer/common/types.h"

/* Borrows an exclusive array of capacity elements; never allocates or frees.
 * The descriptor and its array must not overlap. len <= capacity, and a
 * nonempty array has a non-NULL data pointer. Callers preserve these facts. */
typedef struct {
    vi_token *data;
    size_t len;
    size_t capacity;
} vi_token_buffer;

/* On failure the descriptor is unchanged. Existing array bytes are untouched. */
vi_status vi_token_buffer_init(vi_token_buffer *buffer, vi_token *storage,
                               size_t capacity);

/* First QCP verification target: append exactly one token, preserving the old
 * prefix. Full/invalid buffers are unchanged. No allocation or GPU operation. */
vi_status vi_token_buffer_append(vi_token_buffer *buffer, vi_token token);

#endif
