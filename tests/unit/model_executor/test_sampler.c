#include <math.h>
#include "verifiedinfer/model_executor/sampler.h"
#include "support/check.h"

int main(void)
{
    vi_sample_result result = {.token = 99, .next_state = 101};
    const float logits[] = {1, 5, 5, 0};
    CHECK(vi_sample_greedy(logits, 4, 2, &result) == VI_OK);
    CHECK(result.token == 2 && result.next_state == UINT32_C(1017233273));
    CHECK(vi_sample_greedy(logits, 4, 0, &result) == VI_OK && result.token == 1);
    CHECK(logits[0] == 1 && logits[1] == 5 && logits[2] == 5 && logits[3] == 0);
    const vi_sample_result saved = result;
    const float invalid[] = {0, NAN};
    CHECK(vi_sample_greedy(invalid, 2, 1, &result) == VI_INVALID);
    CHECK(result.token == saved.token && result.next_state == saved.next_state);
    CHECK(vi_sample_greedy(logits, 0, 1, &result) == VI_INVALID);
    CHECK(vi_sample_greedy(NULL, 4, 1, &result) == VI_INVALID);
    const float negative[] = {-9, -2, -3};
    CHECK(vi_sample_greedy(negative, 3, UINT32_MAX, &result) == VI_OK);
    CHECK(result.token == 1);
    puts("PASS: greedy maxima, seeded ties, nonfinite logits and failure preservation");
    return 0;
}
