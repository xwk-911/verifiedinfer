#ifndef VI_COMMON_TYPES_H
#define VI_COMMON_TYPES_H

#include <stddef.h>
#include <stdint.h>

typedef uint32_t vi_token;

typedef enum {
    VI_OK = 0,
    VI_DONE,
    VI_INVALID,
    VI_NO_SPACE,
    VI_MODEL_ERROR
} vi_status;

/* Array sizes must fit bytes and every vocabulary index must fit vi_token. */
static inline int vi_vocab_size_valid(size_t size)
{
    return size != 0 && size <= UINT32_MAX && size <= SIZE_MAX / sizeof(float);
}

#endif
