#ifndef VI_REQUEST_H
#define VI_REQUEST_H

#include <stdbool.h>
#include "verifiedinfer/memory/token_buffer.h"

typedef enum {
    VI_PREFILL = 0,
    VI_DECODE,
    VI_FINISHED,
    VI_FAILED
} vi_phase;

/* Immutable policy; the advancing sampler state lives in vi_request. */
typedef struct {
    size_t max_new_tokens;
    uint32_t initial_sampler_state;
    bool stop_on_eos;
    vi_token eos_token;
    /* Optional additional stopping policy (e.g. multiple EOS IDs from HF).
     * Read-only borrowed array, disjoint from writable history/state and valid
     * for the whole request; independent of
     * the single-EOS switch above. An emitted stop token remains in history. */
    const vi_token *stop_token_ids;
    size_t stop_token_count;
} vi_request_config;

typedef struct {
    vi_token_buffer history;
    size_t prompt_len;
    size_t kv_len;
    size_t vocab_size;
    uint32_t sampler_state;
    vi_request_config config;
    vi_phase phase;
} vi_request;

/* Descriptors and borrowed arrays do not overlap. Invalid input leaves request
 * and storage unchanged; prompt may already be a view of history_storage. */
vi_status vi_request_init(vi_request *request, vi_token *history_storage,
                          size_t history_capacity, const vi_token *prompt,
                          size_t prompt_len, size_t vocab_size,
                          vi_request_config config);

/* Check a stable boundary: PREFILL has no KV; DECODE has one unprocessed token.
 * Terminal requests return DONE/error. */
vi_status vi_request_ready(const vi_request *request);

/* Called after synchronous forward of the entire unprocessed suffix.
 * Append the sample and record completion of the old history's KV.
 * Backend completion is a caller obligation, not proved here. */
vi_status vi_request_commit(vi_request *request, vi_token token,
                            uint32_t next_sampler_state);

#endif
