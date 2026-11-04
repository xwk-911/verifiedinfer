#include <inttypes.h>
#include <stdio.h>

#include "verifiedinfer/engine/engine.h"
#include "verifiedinfer/model_executor/models/mock_model.h"

int main(void)
{
    vi_token history[7], cache[7];
    const vi_token prompt[] = {1, 2, 3};
    vi_mock_model mock;
    vi_model_runner model_runner;
    vi_engine engine;
    float work[8], logits[8];
    vi_output output = {.logits = logits, .logits_capacity = 8};
    vi_request_config config = {.max_new_tokens = 4, .initial_sampler_state = 7,
                                .stop_on_eos = false}; /* Fixed-length demo. */
    if (vi_mock_model_init(&mock, cache, 7, 8, &model_runner) != VI_OK ||
        vi_engine_init(&engine, model_runner, history, 7, work, 8, prompt, 3, config) != VI_OK) {
        return 1;
    }
    puts("Mock model only: cached token IDs and synthetic logits; no neural model.");
    for (;;) {
        const char *phase = engine.request.phase == VI_PREFILL ? "prefill" : "decode";
        vi_status status = vi_engine_step(&engine, &output);
        if (status == VI_DONE) {
            break;
        }
        if (status != VI_OK) {
            fputs("engine step failed\n", stderr);
            return 1;
        }
        printf("%s: token=%" PRIu32 " history=%zu kv=%zu logits=[",
               phase, output.token, engine.request.history.len, engine.request.kv_len);
        for (size_t i = 0; i < output.vocab_size; ++i) {
            printf("%s%.0f", i == 0 ? "" : ",", (double)output.logits[i]);
        }
        puts("]");
    }
    puts("finished (the last sampled token has not been processed into KV)");
    return 0;
}
