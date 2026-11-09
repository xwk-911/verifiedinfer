#ifndef VI_REQUEST_INTERNAL_H
#define VI_REQUEST_INTERNAL_H
#include "verifiedinfer/engine/request.h"

/* Borrows an initialized, read-only config for this call only. The public
 * by-value API keeps its original signature and supplies its own local copy.
 * The config pointer is never retained; the policy values are copied. */
vi_status vi_request_init_config(vi_request *request, vi_token *history_storage,
                          size_t history_capacity, const vi_token *prompt,
                          size_t prompt_len, size_t vocab_size,
                          const vi_request_config *config);
#endif
