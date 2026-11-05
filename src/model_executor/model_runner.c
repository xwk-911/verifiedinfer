#include "model_internal.h"

/* Common synchronous execution boundary; state storage belongs to its architecture. */
static vi_status execute(void *opaque, const vi_model_input *input,
                         float *logits, size_t vocab_size)
{
    vi_model_state *state = opaque;
    if (state == NULL || input == NULL || input->tokens == NULL || logits == NULL ||
        input->count == 0 || vocab_size != state->model->config.vocab_size) return VI_INVALID;
    if (state->failed) return VI_MODEL_ERROR;
    const size_t computed = vi_model_cached_tokens(state);
    if (input->position != computed) return VI_INVALID;
    if (computed > state->capacity || input->count > state->capacity - computed) return VI_NO_SPACE;
    for (size_t i = 0; i < input->count; ++i)
        if (input->tokens[i] >= vocab_size) return VI_INVALID;
    vi_status status = state->model->implementation->executor->forward(
        state->data, input, logits, vocab_size);
    if (status == VI_MODEL_ERROR) state->failed = true;
    return status;
}

void vi_model_runner_bind(vi_model_state *state, vi_model_runner *runner)
{
    runner->state = state;
    runner->forward = execute;
    runner->vocab_size = state->model->config.vocab_size;
}
