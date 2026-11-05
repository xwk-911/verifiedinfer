#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "verifiedinfer/engine/engine.h"
#include "verifiedinfer/model_executor/model.h"

static int parse_size(const char *s, size_t *value)
{
    if (s == NULL || *s == 0 || *s == '-') return 0;
    char *end;
    errno = 0;
    uintmax_t n = strtoumax(s, &end, 10);
    if (errno || *end || n > SIZE_MAX) return 0;
    *value = (size_t)n;
    return 1;
}
static void usage(void)
{
    fputs("Usage: vi-run --model DIR --input TOKEN_IDS.txt [--device cpu|cuda]\n"
          "              [--max-new-tokens N] [--eos ID ...] [--logits FILE]\n"
          "              [--forward-only [--chunks N,N,...]]\n", stderr);
}
int main(int argc, char **argv)
{
    const char *directory = NULL, *input_path = NULL, *logits_path = NULL, *chunks = NULL;
    vi_device device = VI_DEVICE_CPU;
    size_t budget = 16, eos = 0, stop_count = 0;
    vi_token stop_tokens[32];
    bool forward_only = false;
    for (int i = 1; i < argc; ++i) {
        const char *arg = argv[i];
        if (!strcmp(arg, "--forward-only")) { forward_only = true; continue; }
        if (i + 1 == argc) { usage(); return 2; }
        const char *value = argv[++i];
        if (!strcmp(arg, "--model")) directory = value;
        else if (!strcmp(arg, "--input")) input_path = value;
        else if (!strcmp(arg, "--logits")) logits_path = value;
        else if (!strcmp(arg, "--chunks")) chunks = value;
        else if (!strcmp(arg, "--max-new-tokens") && parse_size(value, &budget)) {}
        else if (!strcmp(arg, "--eos") && parse_size(value, &eos) && eos <= UINT32_MAX && stop_count < 32)
            stop_tokens[stop_count++] = (vi_token)eos;
        else if (!strcmp(arg, "--device") && !strcmp(value, "cuda")) device = VI_DEVICE_CUDA;
        else if (!strcmp(arg, "--device") && !strcmp(value, "cpu")) device = VI_DEVICE_CPU;
        else { usage(); return 2; }
    }
    if (!directory || !input_path || (chunks && !forward_only)) { usage(); return 2; }
    char error[512] = {0};
    vi_model *model = NULL;
    vi_model_state *state = NULL;
    vi_token *prompt = NULL, *history = NULL;
    float *work = NULL, *logits = NULL;
    FILE *input_file = NULL, *logits_file = NULL;
    int result = 1;
    if (vi_model_load(directory, device, &model, error, sizeof(error)) != VI_OK) goto done;
    const vi_model_config *config = vi_model_get_config(model);
    input_file = fopen(input_path, "r");
    if (!input_file) { snprintf(error, sizeof(error), "cannot open input IDs"); goto done; }
    size_t count = 0, allocation = 0;
    char token_text[64];
    while (fscanf(input_file, "%63s", token_text) == 1) {
        size_t token;
        if (!parse_size(token_text, &token) || token >= config->vocab_size || count >= config->max_seq_len) {
            snprintf(error, sizeof(error), "invalid token ID or prompt exceeds model context"); goto done;
        }
        if (count == allocation) {
            size_t n = allocation ? allocation * 2 : 64;
            if (n > config->max_seq_len) n = config->max_seq_len;
            if (n > SIZE_MAX / sizeof(*prompt)) { snprintf(error, sizeof(error), "prompt size overflow"); goto done; }
            vi_token *grown = realloc(prompt, n * sizeof(*prompt));
            if (!grown) { snprintf(error, sizeof(error), "prompt allocation failed"); goto done; }
            prompt = grown; allocation = n;
        }
        prompt[count++] = (vi_token)token;
    }
    if (ferror(input_file) || count == 0 || (!forward_only && budget > config->max_seq_len - count)) {
        snprintf(error, sizeof(error), "empty/invalid input or generation budget exceeds model context"); goto done;
    }
    size_t capacity = count + (forward_only ? 0 : budget);
    if (capacity > SIZE_MAX / sizeof(vi_token)) { snprintf(error, sizeof(error), "history size overflow"); goto done; }
    work = malloc(config->vocab_size * sizeof(float));
    logits = malloc(config->vocab_size * sizeof(float));
    history = malloc(capacity * sizeof(vi_token));
    if (!work || !logits || !history) { snprintf(error, sizeof(error), "output/history allocation failed"); goto done; }
    vi_model_runner runner;
    if (vi_model_state_create(model, capacity, &state, &runner, error, sizeof(error)) != VI_OK) goto done;
    if (logits_path) {
        logits_file = fopen(logits_path, "wb");
        if (!logits_file) { snprintf(error, sizeof(error), "cannot create logits file"); goto done; }
    }
    if (forward_only) {
        size_t position = 0;
        char *partition = chunks ? strdup(chunks) : NULL, *save = NULL;
        if (chunks && !partition) { snprintf(error, sizeof(error), "chunk allocation failed"); goto done; }
        char *part = partition ? strtok_r(partition, ",", &save) : NULL;
        do {
            size_t n = count - position;
            if ((part && !parse_size(part, &n)) || n == 0 || n > count - position) {
                free(partition); snprintf(error, sizeof(error), "invalid chunk partition"); goto done;
            }
            vi_model_input input = {.tokens = prompt + position, .count = n, .position = position};
            if (runner.forward(runner.state, &input, logits, runner.vocab_size) != VI_OK) {
                free(partition); snprintf(error, sizeof(error), "forward failed"); goto done;
            }
            position += n;
            part = partition ? strtok_r(NULL, ",", &save) : NULL;
        } while (part);
        free(partition);
        if (position != count) { snprintf(error, sizeof(error), "chunk partition does not cover prompt"); goto done; }
        if (logits_file && fwrite(logits, sizeof(float), config->vocab_size, logits_file) != config->vocab_size) {
            snprintf(error, sizeof(error), "cannot write logits"); goto done;
        }
        printf("{\"cached_tokens\":%zu,\"vocab_size\":%zu}\n", vi_model_cached_tokens(state), config->vocab_size);
    } else {
        vi_engine engine;
        vi_output output = {.logits = logits, .logits_capacity = config->vocab_size};
        vi_request_config request = {.max_new_tokens = budget,
            .stop_token_ids = stop_tokens, .stop_token_count = stop_count};
        if (vi_engine_init(&engine, runner, history, capacity, work, config->vocab_size, prompt, count, request) != VI_OK) {
            snprintf(error, sizeof(error), "engine initialization failed"); goto done;
        }
        for (;;) {
            vi_status status = vi_engine_step(&engine, &output);
            if (status == VI_DONE) break;
            if (status != VI_OK) { snprintf(error, sizeof(error), "engine step failed (status %d)", status); goto done; }
            if (logits_file && fwrite(logits, sizeof(float), output.vocab_size, logits_file) != output.vocab_size) {
                snprintf(error, sizeof(error), "cannot write logits"); goto done;
            }
            printf("{\"token\":%" PRIu32 ",\"kv_len\":%zu}\n", output.token, engine.request.kv_len);
            fflush(stdout);
        }
    }
    result = 0;
done:
    if (input_file) fclose(input_file);
    if (logits_file && fclose(logits_file) != 0) { snprintf(error, sizeof(error), "logits close failed"); result = 1; }
    if (result) fprintf(stderr, "vi-run: %s\n", error[0] ? error : "operation failed");
    vi_model_state_free(state);
    vi_model_free(model);
    free(prompt); free(history); free(work); free(logits);
    return result;
}
