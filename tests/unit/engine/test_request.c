#include "verifiedinfer/engine/request.h"
#include "support/check.h"

static void test_request_transitions(void)
{
    vi_token storage[4];
    const vi_token prompt[] = {1, 2};
    vi_request request;
    vi_request_config config = {.max_new_tokens = 2, .initial_sampler_state = 19};
    CHECK(vi_request_init(&request, storage, 4, prompt, 2, 8, config) == VI_OK);
    CHECK(vi_request_ready(&request) == VI_OK && request.phase == VI_PREFILL);
    CHECK(request.sampler_state == 19 && request.kv_len == 0);

    /* Completion of forward is an explicit caller premise of commit. */
    CHECK(vi_request_commit(&request, 4, 23) == VI_OK);
    CHECK(request.phase == VI_DECODE && request.kv_len == 2 && request.history.len == 3);
    CHECK(request.sampler_state == 23 && request.config.initial_sampler_state == 19);
    CHECK(storage[0] == 1 && storage[1] == 2 && storage[2] == 4);
    CHECK(vi_request_commit(&request, 5, 29) == VI_OK);
    CHECK(request.phase == VI_FINISHED && request.kv_len == 3 && request.history.len == 4);
    CHECK(vi_request_commit(&request, 6, 31) == VI_DONE && request.sampler_state == 29);
}

static void test_invalid_commit_is_atomic(void)
{
    vi_token storage[] = {91, 92};
    const vi_token prompt[] = {1};
    vi_request request;
    CHECK(vi_request_init(&request, storage, 2, prompt, 1, 8,
                          (vi_request_config){.max_new_tokens = 1,
                                              .initial_sampler_state = 7}) == VI_OK);
    CHECK(vi_request_commit(&request, 8, 19) == VI_INVALID);
    CHECK(storage[1] == 92 && request.history.len == 1 && request.kv_len == 0);
    CHECK(request.sampler_state == 7 && request.phase == VI_PREFILL);
    request.kv_len = 1;
    CHECK(vi_request_ready(&request) == VI_INVALID);
    CHECK(vi_request_commit(&request, 2, 19) == VI_INVALID);
    CHECK(storage[1] == 92 && request.sampler_state == 7);
}

int main(void)
{
    test_request_transitions();
    test_invalid_commit_is_atomic();
    puts("PASS: request transitions, immutable policy and invalid commit");
    return 0;
}
