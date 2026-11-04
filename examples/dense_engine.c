#include <inttypes.h>
#include <stdio.h>

#include "verifiedinfer/engine/engine.h"
#include "tiny_dense_weights.h"

int main(void)
{
    float weight_storage[TINY_WEIGHTS];
    vi_dense_weights weights;
    float keys[TINY_KV], values[TINY_KV], workspace[TINY_WORKSPACE];
    float logits_workspace[TINY_VOCAB], logits[TINY_VOCAB];
    vi_token history[7];
    const vi_token prompt[] = {1, 2, 3};
    vi_dense_model model;
    vi_model_runner runner;
    vi_engine engine;
    vi_output output = {.logits = logits, .logits_capacity = TINY_VOCAB};
    const vi_request_config config = {.max_new_tokens = 4,
        .initial_sampler_state = 7, .stop_on_eos = false}; /* Fixed-length demo. */
    if (tiny_dense_weights_init(&weights, weight_storage) != VI_OK ||
        vi_dense_model_init(&model, &weights, keys, values, TINY_KV,
                            workspace, TINY_WORKSPACE, &runner) != VI_OK ||
        vi_engine_init(&engine, runner, history, 7, logits_workspace, TINY_VOCAB,
                       prompt, 3, config) != VI_OK) {
        return 1;
    }
    puts("Tiny dense Transformer: CPU, one layer/head, real K/V, untrained weights.");
    for (;;) {
        const char *phase = engine.request.phase == VI_PREFILL ? "prefill" : "decode";
        vi_status status = vi_engine_step(&engine, &output);
        if (status == VI_DONE) {
            break;
        }
        if (status != VI_OK) {
            fputs("dense engine step failed\n", stderr);
            return 1;
        }
        printf("%s: token=%" PRIu32 " history=%zu kv=%zu selected_logit=%.7g\n",
               phase, output.token, engine.request.history.len,
               model.cache.len, (double)output.logits[output.token]);
    }
    return 0;
}
