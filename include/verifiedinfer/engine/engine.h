#ifndef VI_ENGINE_H
#define VI_ENGINE_H

#include "verifiedinfer/engine/request.h"
#include "verifiedinfer/model_executor/model_runner.h"

typedef struct {
    vi_request request;
    vi_model_runner model_runner;
    float *logits_workspace;
    size_t logits_capacity;
} vi_engine;

typedef struct {
    float *logits;
    size_t logits_capacity;
    size_t vocab_size;
    vi_token token;
} vi_output;

/* Own descriptors/output separately from borrowed history, logits workspace,
 * and model storage; all writable arrays are disjoint. Model state is fresh
 * and exclusive. Weights may be shared read-only between requests.
 * A nonempty prompt and enough space for the full generation budget are needed.
 * max_new_tokens == 0 creates an already-finished request. */
vi_status vi_engine_init(vi_engine *engine, vi_model_runner model_runner,
                         vi_token *history_storage, size_t history_capacity,
                         float *logits_workspace, size_t logits_capacity,
                         const vi_token *prompt, size_t prompt_len,
                         vi_request_config config);

/* PREFILL consumes the prompt; DECODE consumes the last sampled token.
 * At each successful output boundary kv_len + 1 == history.len: the newly
 * sampled token has not been forwarded yet (fields live in engine.request).
 * Caller supplies output->logits with at least vocab_size elements. The output
 * descriptor and its logits are unchanged on failure. Logits workspace may be
 * overwritten. Detected nonfinite logits make the engine terminally FAILED;
 * arbitrary violations by foreign model implementations cannot be detected. */
vi_status vi_engine_step(vi_engine *engine, vi_output *output);

#endif
